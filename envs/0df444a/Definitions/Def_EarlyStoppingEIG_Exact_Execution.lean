-- Prove2me | Definitions.Def_EarlyStoppingEIG_Exact_Execution
-- name    : EarlyStoppingEIG_Exact_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:01.919989+00:00
-- url     : https://prove2.me/theorems/379737e0-dc74-4c76-8d32-948e6012acd3
-- title:
--   Strongly adaptive authenticated synchronous executions
-- statement:
--   An execution is a finite list of atomic events in each synchronous round: corruption, honest signing, individual channel sends, deliveries and deletions. Corruption reveals the party’s memory and enables its signing key from that event onward. A faulty party may send any currently derivable wire term, including malformed data, with arbitrary omission or equivocation. Honest messages already sent can be deleted after the sender is corrupted. Honest active behavior and honest channel deadlines are imposed before the end-of-round local transition.
--
--   $$F=\{i:\text{a corruption of }i\text{ occurs in the trace}\},\qquad f=|F|\le t.$$
--
--   The bound is a consequence of the corruption-event budget and monotonicity. Never-corrupted parties are honest. Halting means output plus permanent cessation of honest communication. No agreement, equal-entry lemma, early termination bound or correctness certificate is a field of an execution. The only non-idle rounds are protocol rounds through $t+1$.
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), §2 and §3.2, pp.15–18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_Protocol

namespace EarlyStoppingEIG.Exact

structure Packet (P : Parameters) where
  sender : Party P
  recipient : Party P
  body : Message P

/-- Operational state during a round. Corruption is monotone, and exposed
knowledge consists only of traffic already exposed and memories already
compromised. Pending packets permit corruption after sending but before delivery. -/
structure World (P : Parameters) where
  views : Party P → LocalView P
  corrupt : Finset (Party P)
  exposed : Set (Message P)
  pending : List (Packet P)
  sentTo : Finset (Party P × Party P)

def initialWorld (P : Parameters) : World P :=
  ⟨fun _ => emptyView P, ∅, ∅, [], ∅⟩

def exposedMemory (P : Parameters) (v : LocalView P) : Set (Message P) :=
  {m | (∃ r, v.own r = some m) ∨ ∃ r j, v.receipt r j = some m}

inductive Action (P : Parameters) where
  | corrupt : Party P → Action P
  | sign : Party P → ℕ → Action P
  | send : Packet P → Action P
  | deliver : Packet P → Action P
  | delete : Packet P → Action P

/-- Atomic actions within a synchronous round. An honest signing operation is
separate from its individual sends, so corruption can interrupt a sending
sequence. The adversary can sign with a key only after corrupting its owner,
and can replay a previously exposed signature. The relation neither mentions
the desired bound nor any agreement/entry lemma. -/
inductive ActionStep (P : Parameters) (b : Bool) (r : ℕ) :
    World P → Action P → World P → Prop where
  | corrupt (X : World P) (i : Party P)
      (fresh : i ∉ X.corrupt) (budget : (insert i X.corrupt).card ≤ P.t) :
      ActionStep P b r X (.corrupt i)
        { X with corrupt := insert i X.corrupt
                 exposed := X.exposed ∪ exposedMemory P (X.views i) }
  | sign (X : World P) (i : Party P) (nonce : ℕ)
      (honest : i ∉ X.corrupt)
      (active : RequiredToSend P i (X.views i) r)
      (once : (X.views i).own r = none) :
      ActionStep P b r X (.sign i nonce)
        { X with views := Function.update X.views i (recordOwn P i r
            (honestSigned P b i (X.views i) r nonce) (X.views i)) }
  | send (X : World P) (a : Packet P)
      (allowed :
        (a.sender ∈ X.corrupt ∧ Derivable (↑X.corrupt : Set (Party P)) X.exposed a.body) ∨
        (a.sender ∉ X.corrupt ∧ RequiredToSend P a.sender (X.views a.sender) r ∧
          (X.views a.sender).own r = some a.body ∧ a.sender ≠ a.recipient ∧
          (a.sender, a.recipient) ∉ X.sentTo)) :
      ActionStep P b r X (.send a)
        { X with exposed := insert a.body X.exposed
                 pending := X.pending ++ [a]
                 sentTo := insert (a.sender, a.recipient) X.sentTo }
  | deliver (X : World P) (a : Packet P) (before after : List (Packet P))
      (queued : X.pending = before ++ [a] ++ after) :
      ActionStep P b r X (.deliver a)
        { X with pending := before ++ after
                 views := Function.update X.views a.recipient
                   (receive P a.sender r a.body (X.views a.recipient)) }
  | delete (X : World P) (a : Packet P) (before after : List (Packet P))
      (queued : X.pending = before ++ [a] ++ after) (compromised : a.sender ∈ X.corrupt) :
      ActionStep P b r X (.delete a) { X with pending := before ++ after }

inductive RoundActions (P : Parameters) (b : Bool) (r : ℕ) :
    World P → List (Action P) → World P → Prop where
  | nil (X) : RoundActions P b r X [] X
  | cons {X Y Z a rest} : ActionStep P b r X a Y →
      RoundActions P b r Y rest Z → RoundActions P b r X (a :: rest) Z

/-- Honest sends and channel deadlines are checked before the views stopping
transition. A message already sent by a subsequently corrupted party can be
deleted; one from a still honest sender to an active honest receiver cannot be
discarded. Pending faulty traffic may be omitted at the deadline. -/
def RoundReady (P : Parameters) (r : ℕ) (X : World P) : Prop :=
  (∀ i, i ∉ X.corrupt → RequiredToSend P i (X.views i) r →
    ((X.views i).own r).isSome ∧ ∀ j, j ≠ i → (i, j) ∈ X.sentTo) ∧
  ∀ a ∈ X.pending, a.sender ∉ X.corrupt → a.recipient ∉ X.corrupt →
    (X.views a.recipient).halt = none → False

noncomputable def closeWorld (P : Parameters) (b : Bool) (r : ℕ) (X : World P) : World P :=
  { X with views := fun i => if i ∈ X.corrupt then X.views i else closeLocal P b i r (X.views i)
           pending := []
           sentTo := ∅ }

/-- An execution contains the actual finite action list in every round and
the end-of-round states. No future transcript is a party input. -/
structure Execution (P : Parameters) where
  state : ℕ → World P
  actions : ℕ → List (Action P)

def IsExecution (P : Parameters) (b : Bool) (E : Execution P) : Prop :=
  E.state 0 = initialWorld P ∧
  (∀ q, P.t + 1 < q → E.actions q = []) ∧ ∀ r, ∃ X,
    RoundActions P b (r + 1) (E.state r) (E.actions (r + 1)) X ∧
    RoundReady P (r + 1) X ∧ E.state (r + 1) = closeWorld P b (r + 1) X

/-- The actual faulty set is derived from corruption events, over the entire
execution, and is not supplied to the protocol. -/
noncomputable def faulty (P : Parameters) (E : Execution P) : Finset (Party P) := by
  classical
  exact Finset.univ.filter (fun i => ∃ r, i ∈ (E.state r).corrupt)

def Honest (P : Parameters) (E : Execution P) (i : Party P) : Prop :=
  ∀ r, i ∉ (E.state r).corrupt

def Active (P : Parameters) (E : Execution P) (i : Party P) (r : ℕ) : Prop :=
  1 ≤ r ∧ ((E.state (r - 1)).views i).halt = none

def HaltsAt (P : Parameters) (E : Execution P) (i : Party P) (r : ℕ) (b : Bool) : Prop :=
  ((E.state r).views i).halt = some (r, b)

def Outputs (P : Parameters) (E : Execution P) (i : Party P) (b : Bool) : Prop :=
  ∃ r, HaltsAt P E i r b

def HaltsBy (P : Parameters) (E : Execution P) (i : Party P) (R : ℕ) : Prop :=
  ∃ r b, r ≤ R ∧ HaltsAt P E i r b

def ReceiptAt (P : Parameters) (E : Execution P) (i : Party P) (u : ℕ) (j : Party P) : Receipt P :=
  ((E.state u).views i).receipt u j

def SentAt (P : Parameters) (E : Execution P) (j : Party P) (u : ℕ) (m : Message P) : Prop :=
  ((E.state u).views j).own u = some m

end EarlyStoppingEIG.Exact


