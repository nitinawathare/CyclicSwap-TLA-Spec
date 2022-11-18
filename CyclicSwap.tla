----------------------------- MODULE CyclicSwap -----------------------------


CONSTANT RM  \* The set of aprties involved in the swap

VARIABLES
  rmState,       \* rmState[r] is the state of party r.
  receivedSecret,    \* rmState[r] The set of RMs from which r receives the secrete"
                 
  msgs           
    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  For simplicity, we represent message passing with the    *)
    (* variable msgs whose value is the set of all messages that have been *)
    (* sent.  A message is sent by adding it to the set msgs.  An action   *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the presence of that message in  *)
    (* msgs.  For simplicity, messages are never removed from msgs.        *)

Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "secrete"  are    *)
  (* sent from the RM indicated by the message's rm field to the other RMs.*)
  (*************************************************************************)
  [type : {"secret"}, rm : RM] 
   
CSTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"init", "commit", "refund", "payment"}]
  /\ \A r \in RM: receivedSecret[r] \subseteq RM
  /\ msgs \subseteq Messages

CSInit ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [r \in RM |-> "init"]
  /\ receivedSecret = [r \in RM |-> {}]
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* Now each party receives secrete from every other party, which is noted  *)
(* which is noted in the receivedSecret                                    *)
(***************************************************************************)
RMRcvSecret(r, r_s) ==
  /\ rmState[r] = "init"
  /\ [type |-> "secret", rm |-> r_s] \in msgs
  /\ receivedSecret' = [receivedSecret EXCEPT ![r] = receivedSecret[r] \cup {r_s}]
  /\ UNCHANGED <<rmState, msgs>>

RMCommit(r) ==
  (*************************************************************************)
  (* Each party moves to the commit state, if it receives the secret from  *)
  (* all other parties involved in the swap                                *)
  (*************************************************************************)
  /\ rmState[r] = "init"
  /\ receivedSecret[r] = RM
  /\ rmState' = [rmState EXCEPT ![r] = "commit"]
  /\ UNCHANGED <<receivedSecret, msgs>>

RMRefund(r) ==
  (*************************************************************************)
  (* If party doesn't receive the secret from all other parties involved in *)
  (* the swap while some party has receivesd it and moved to the commit state*)
  (*************************************************************************)
  /\ rmState[r] = "init"
  /\ \E r_s \in RM: rmState[r_s]="commit"
\*  /\ \A r_s \in RM: rmState[r_s]#"payment"
  /\ receivedSecret[r] # RM
  /\ rmState' = [rmState EXCEPT ![r] = "refund"]
  /\ UNCHANGED <<receivedSecret, msgs>>

RMPayment(r) ==
  (*************************************************************************)
  (* If all there doesn't exist any party that moved to the commit set then *)
  (* party r will terminate the protocol and moves to the payment state     *)
  (*************************************************************************)
  /\ rmState[r] = "commit"
  /\ \A r_s \in RM: rmState[r_s] = "commit"
  /\ rmState' = [rmState EXCEPT ![r] = "payment"]
  /\ UNCHANGED <<receivedSecret, msgs>>


RMSendSecret(r) == 
  (*************************************************************************)
  (* Resource manager r prepares.                                          *)
  (*************************************************************************)
  /\ rmState[r] = "init"
  /\ msgs' = msgs \cup {[type |-> "secret", rm |-> r]}
  /\ UNCHANGED <<rmState, receivedSecret>>


CSNext ==
  \/ \E r \in RM : 
       RMCommit(r) \/ RMRefund(r) \/ RMSendSecret(r) \/ RMPayment(r)
  \/ \E r, n \in RM :  RMRcvSecret(r, n)     


CSConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.  It is an invariant of the specification.      *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "payment"
                       /\ rmState[r2] = "refund"
 

(************************************END of the Code here **************************************)
 

=============================================================================
\* Modification History
\* Last modified Fri Nov 18 11:01:31 SGT 2022 by nitina
\* Created Tue Nov 15 12:04:31 SGT 2022 by nitina
