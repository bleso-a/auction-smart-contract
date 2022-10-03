# Building an Auction Smart Contract with Scilla Programming Language

## Quick Summary
This smart contract is written in the Scilla programming language containing three transitions, allowing three different activities to take place during and after the auctioning. The first transition allows bidding to take place while taking note of some constraints; the second transition allows the users to withdraw funds by claiming their money back in the case of pending returns; the last transition is for the auction to end, and the owner takes the highest bid. 

The first transition is a bit complex as it is used to track so many constraints while placing the bid. In this transition, pattern matching is used, and there are four pattern scopes, with each operation set to meet the bidding constraints. 

The second transition is more straightforward, and it is used to set a strict withdrawal pattern that is necessary to prevent an attack and avoid re-entrancy bugs. Scilla already helps with this by preventing transitions from being interrupted to ensure no re-entrancy bugs. We can use the withdrawal transition to send pending funds to bidders and track when not to send funds.

The third transition is also relatively straightforward; it tracks timestamps in terms of block number, just like in the first transition. The values are used in the pattern matching, determining when the auction ends. Finally, the beneficiary will receive the highest bid amount when the _pattern_ value is True. 

---

## Detailed Explanation plus Code Walkthrough

I will explain more by going through each code section, the code logic, and the intuition behind each implementation. 

---

### Starting with the Library

Before I describe the library in the auctioning programming, let’s talk about the Scilla version in the first line - `scilla_version 0`. It is a way to specify the version of Scilla that we are working with, which is `0`. 

The next line imports `BoolUtils` - one of the Scilla standard libraries out of five. The `BoolUtils` library implements boolean utility operations, and we will use it to perform some logical operations and comparisons in the rest of the contract. 

The following code section starts the library implementation, which is user-defined. The library is used to store program constants, constructs, and utility functions with a scope that covers the entire auction contract. 

By using the keyword `library` followed by the name of the library `OpenAuction`, we begin the implementation. 


#### `blk_leq` library function
```
let blk_leq =
  fun (blk1 : BNum) =>
  fun (blk2 : BNum) =>
    let bc1 = builtin blt blk1 blk2 in 
    let bc2 = builtin eq blk1 blk2 in 
    orb bc1 bc2
```

The code section is a `blk_leq` library function that takes two blocks (blk1, blk2). The function defines two variables, `bc1` and `bc2`. For bc1, if `blk1` is less than `blk2`, then `bc1` is set to true. For `bc2`, if `blk1` is equal to `blk2,` then `bc2` is set to true. From the imported `BoolUtils`, we will use the `Orb` method that computes the logical `OR` of two `Bool` values, in this case, `bc1` and `bc2`. This library function will help compare blocks for auction constraints set later. 




#### `one_msg` library function

```
let one_msg = 
  fun (msg : Message) => 
    let nil_msg = Nil {Message} in
    Cons {Message} msg nil_msg
```

The code block implements the one_msg library function to construct a list containing one message. To send messages to the users, for example, in the case of early bidding, we will use the `one_msg` construct with the list functionality. 

#### Construct a Message
We need to understand how to construct a message; we will use it to send messages when certain things happen; for example, when the users bid too early, we send a message that contains the `too_early_to_bid_code` code. 

To construct a message, we use the following syntax; 

```
msg = {_tag: "abc"; _recipient: abc; _amount: abc; code: abc};

```
Where `_tag`, `_recipient`, and `_amount` are the compulsory field, the `_recipient` field is the blockchain address to which the message is sent, and the `_amount` field is the number of ZIL to be transferred to that account. The value of the `_tag` field is the name of the transition invoked on the`_recipient` contract. 

#### Constants
```
​​let late_to_bid_code = Int32 1
let too_early_to_bid_code = Int32 2
let bid_too_low_code = Int32 3
let first_bid_accepted_code  = Int32 4
let bid_accepted_code  = Int32 5
let money_sent_code  = Int32 6
let nothing_to_withdraw_code  = Int32 7
let auction_is_still_on_code  = Int32 8
let auction_end_code  = Int32 9
```
The library uses constants to describe error codes, as shown in the code block above. The constants are self-explanatory and descriptive. 

---

### Contract Definition 


#### Immutable Variables 

Any contract deployed on the blockchain is immutable; we need to keep this in mind at the start of the contract implementation, hence why we need to set immutable variables. Once initialized, the values of these parameters will not change. We need to set three parameters as immutable variables: `auctionStart`, `biddingTime`, and `beneficiary`. 

An auction requires a start and end time, **_but it is tricky to use timestamps because of security purposes, hence why we will use block number instead._** So, the `auctionStart` will be of type `BNum` - Block Number; it is an excellent practice to infer timestamps from block numbers rather than normal timestamps. 
The `biddingTime` is of type `Uint128`. The `beneficiary` is the person the funds will go to after the auction. It is of type `ByStr20`, representing the beneficiary's address. 

#### Mutable Variables
We usually need variables whose values will be altered by the code in the contract to perform actions on data. These variables are called mutable variables since they can be modified while still being stored on the blockchain. For this auction project, we need to define a few mutable variables, as shown in the code block below.

To define mutable variables, we follow this format `field variableName: variableType = "Variable TextValue"`

```
field ended : Bool = False
field highestBidder  : Option ByStr20  = None {ByStr20}
field highestBid     : Uint128 = Uint128 0
field pendingReturns : Map ByStr20 Uint128 = Emp ByStr20 Uint128

```

The `ended` variable represents a boolean type whose value is set as `False` and is used to determine when the auction will end. The `highestBidder` stores the address of the highest bidder and is set to `None` while the `highestBid` represents the highest bid amount. 

`pendingReturns` is a map type of `kt vt` that provides a key-value store where `kt` is the type of keys and `vt` is the type of values. In this case, we have the address type and amount type, whose values are empty for now. We need `pendingReturns` to track anything you send more than the bidding value, which will be refunded to the users after completing the auction. 

---
### Transitions


For a smart contract to be genuinely functional, the blockchain code must be able to communicate with the outside world. It requires some interfaces so that commands, data, or tokens can be sent to or requested from the smart contract. 
In Scilla, we use transitions; you can think of them as functions in other languages. 

#### A. Bid Transition
This transition is used to place a bid. In this transition, we take certain conditions when placing a bid. Placing a bid should only be possible in some instances - it shouldn’t be allowed when the auction is canceled, before, and after it ends. 


```
  blk <- & BLOCKNUMBER;
  endtime = builtin badd auctionStart biddingTime;
  after_end = let one = Uint128 1 
    in builtin badd endtime one;
  e <- ended;
  in_time = blk_leq after_end blk;
  flag1 = orb in_time e;
  early = blk_leq blk auctionStart;
```

The part above represents tracking the block number for when the auction starts, the block after the auction ends, and the block during the auction. 

Going by the explanation of the `blk_leq` library function above, we can infer that if `after_end` is less than `blk` then `bc1` is true. If `after_end` is equal to `blk` then `bc2` is true. So, `in_time` is true if `after_end` is less than `blk` or if `after_end` is equal to `blk`. The logic makes sense because we are tracking the block outside the constraints where users can not place a bid. The same logic goes for the `early` variable. 



##### Pattern Matching (Bid Transition)
At some point, we need the transition to take a different path depending on the output of some conditions we are tracking. In Scilla, we use pattern matching to achieve this; we need to implement certain logic if certain conditions are true or not. The pattern matching in the first transition is a bit convoluted, but we have four pattern scopes; `early`, `flag1`, `sufficientBid`, and `hbPrev`. 
Each pattern scope handles different conditions, and breaking it down into these scopes could help to understand. I will explain a few actions that are going on in each scope below; 

In the auction contract, we need to be able to tell the user when it is too early to bid and it is too late to bid; if the conditions we met, then we have the highest bid amount, which is set to `hb`

The code below is the pattern matching part that handles the condition above.

```
  | True =>
    msg  = {_tag : ""; _recipient : _sender; _amount : Uint128 0; code : too_early_to_bid_code};
    msgs = one_msg msg;
    send msgs
  | False =>
    match flag1 with
    | True => 
      msg  = {_tag : ""; _recipient : _sender; _amount : Uint128 0; code : late_to_bid_code};
      msgs = one_msg msg;
      send msgs
    | False =>
      hb <- highestBid;
```


Consequently, if the bid amount is too low, we send the `bid_too_low_code` with the message. Otherwise, we accept the bid if it meets the `sufficientBid` condition and set it to the `hbPrev` because we already have the highest bidder. 

The code block below implements the logic above.

```
      (* Checks if the bid is too low *)
      sufficientBid = builtin lt hb _amount;
      match sufficientBid with 
      | False =>
        msg  = {_tag : ""; _recipient : _sender; _amount : Uint128 0; code : bid_too_low_code};
        msgs = one_msg msg;
        send msgs
      | True =>
        accept;
        hbPrev <- highestBidder;
```

The last part of the pattern matching takes care of the pending returns.

```
(* Update the highest bidder *)
      bidder = Some {ByStr20} _sender;
      highestBidder := bidder;
      highestBid := _amount;
      ev = {_eventname: "Bid"; code: bid_accepted_code; addr: _sender; amount: _amount};
      event ev
```

The code block above updates the highest bidder's address and amount and finally emits an event to the blockchain. This happens within the scope of the `sufficientBid` pattern matching. 

Within the scope of `flag1` pattern matching, if the condition is `None`, then we need to process the first bid, by updating the `first_bidder address`, and `highestBid`, which is an implicit `_amount`. Finally, we emit an event to the blockchain with the `first_bid_accepted_code` and other parameters.  

#### B. Withdraw Transition
We need to implement a withdrawal pattern to help against any attack and re-entrance bugs. This part of the contract takes care of that. 

```
  prs <- pendingReturns;
  pr = builtin get prs _sender;
```
In the code above, after setting the `pendingReturns` map to the `prs` variable, and we use the `get` map function to get senders. 

##### Pattern Matching (Withdraw Transition)
The pattern matching here is quite straightforward, we have two pattern scopes, similar to the if-then pattern. 

If the `pr` value is `None` then we should send a message with the `nothing_to_withdraw_code`. If we have some value, we delete the sender, emit an event to the blockchain, and send a message with the `money_sent_code`. 

#### C. Auction Ends Transition.

In this transition, we will track the timestamps, as usual, using the block number. We are also using some `BoolUtils` operators; `negb` and `andb`. The `negb` operator is used to change the value of `e` that was set to `False` at the beginning of the contract to `True`, so that we can determine if the auction is still on within the `t4` pattern scope. 

At the end of the auction, we set the `ended` to `True`, emit an event that the auction has ended, and send the `amount` to the `beneficiary` address with a message code `auction_end_code`
