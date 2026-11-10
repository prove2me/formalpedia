-- Prove2me | Definitions.Def_ChoiSemiHonestMPC_OTUpper_Network
-- name    : ChoiSemiHonestMPC_OTUpper_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:28:21.410196+00:00
-- url     : https://prove2.me/theorems/e757ca57-0726-442f-aac3-c8f757e522aa
-- title:
--   The synchronous client–server network with erasures and adaptive passive corruption
-- statement:
--   The synchronous private-channel network of Section 2.1 has Alice, Bob and n labelled servers. A program has local send, randomized compute, receive and separate erase operations; the delivery-gated erase operation waits for outstanding sends from that party to be delivered, as Figure 5 requires; ordinary state replacement can erase without this gate in other protocols. An unbounded passive adversary chooses local operations, message receipts (including a selected sender), and corruptions from its observations and auxiliary input. Private traffic of honest parties is hidden. A first corruption reveals current unerased state; later sends, computations and receipts of that party are observed. Corruption is permanent, with a budget of at most one client and t servers. The adversary has any fixed finite number of scheduling slots per round; forced passes complete the round at the deadline, and final corruption slots follow execution. Synchronous states that an abstract program’s declared round bound actually completes all operations and deliveries, under every adversary. Bit communication sums message lengths, with each message counting at least one bit; message communication counts sends. Every empty program send is padded to one zero bit on the wire, so actual message lengths equal their charged lengths.
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Section 2.1 and Table 3, p. 12, 33 (PDF 14, 35)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Prob

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- The parties of the client–server model (Section 2.1): the clients Alice and Bob and
`n` servers with unique labels `0, …, n-1` (the paper's `[n]`, shifted to `Fin n`). -/
inductive Party (n : ℕ) where
  | alice
  | bob
  | server (i : Fin n)
  deriving DecidableEq

/-- The two clients. -/
inductive Client where
  | alice
  | bob
  deriving DecidableEq

/-- A client as a party. -/
def Client.toParty {n : ℕ} : Client → Party n
  | .alice => .alice
  | .bob => .bob

/-- Program messages are bit strings. The network pads an empty send with one zero
bit, so every delivered and charged message is nonempty as required in Section 2.1. -/
abbrev Msg := List Bool

/-- Wire representation of a send: even a control message carries at least one bit. -/
def wireMsg (m : Msg) : Msg := if m.isEmpty then [false] else m

/-- One local operation of a party: sending a message (with the state after sending), or a
local (possibly randomized) computation on its private state, or an erasure. An erasure
waits for this party's outstanding sends to be delivered and replaces its state; a
corruption can fall between a send, a receipt and an erasure. -/
inductive Op (n : ℕ) (S : Type) where
  | send (dst : Party n) (m : Msg) (s' : S)
  | compute (k : PMF S)
  | erase (s' : S)

/-- A synchronous protocol for two clients and `n` servers.  Every party runs the
randomized program `act` on its own private state `S` (it may depend on the public round
number); `act p r s = none` means `p` has nothing more to do in round `r`.  `recv` is the
state update when a message is received.  Clients start from their inputs, servers from
their labels; local randomness is drawn by `compute` operations, so it is part of the
state until erased.  `outA`/`outB` read the clients' outputs (`none` is the abort
symbol `⊥`).  `opBound` bounds the operations a party performs in one round; at a round
deadline the remaining operations are completed (see `runRound`). -/
structure Protocol (n : ℕ) (IA IB OA OB : Type) where
  S : Type
  initA : IA → S
  initB : IB → S
  initS : Fin n → S
  rounds : ℕ
  opBound : ℕ
  act : Party n → ℕ → S → Option (Op n S)
  recv : Party n → ℕ → S → Party n → Msg → S
  outA : S → Option OA
  outB : S → Option OB

/-- A scheduling or corruption decision of the adversary: let party `p` perform its next
local operation, let `p` receive its oldest pending message (optionally from a selected sender), corrupt
`p`, or do nothing.
A decision that does not apply (nothing to do, budget exhausted) has no effect. -/
inductive Decision (n : ℕ) where
  | act (p : Party n)
  | recv (p : Party n)
  | recvFrom (p fr : Party n)
  | corrupt (p : Party n)
  | pass

/-- Entries of the adversary's view: its own decisions, the current state of a party at
the moment it is corrupted, and every later local observation of a corrupted party (a
message it sends, a computation step, a message it receives, each with the new state), and
the public round clock.  Nothing about honest parties' operations is recorded. -/
inductive Event (n : ℕ) (S : Type) where
  | decided (d : Decision n)
  | reveal (p : Party n) (s : S)
  | sent (p : Party n) (dst : Party n) (m : Msg) (s' : S)
  | computed (p : Party n) (s' : S)
  | received (p : Party n) (fr : Party n) (m : Msg) (s' : S)
  | roundEnd (r : ℕ)

/-- A passive, adaptive, rushing adversary, computationally unbounded, with auxiliary
input of type `Aux`: a behavioural strategy mapping its auxiliary input and its view so far
to a distribution over decisions, with `slots` decisions per round before the round
deadline.  Corrupted parties keep following the protocol (passive). -/
structure Adversary (n : ℕ) (S : Type) (Aux : Type) where
  slots : ℕ
  strat : Aux → List (Event n S) → PMF (Decision n)

/-- A global configuration of an execution. `log` records every message ever sent
(round, sender, receiver, content); it is not visible to the adversary and is used only to
count communication. -/
structure Config (n : ℕ) (S : Type) where
  st : Party n → S
  inflight : List (Party n × Party n × Msg)
  corrupted : List (Party n)
  round : ℕ
  hist : List (Event n S)
  log : List (ℕ × Party n × Party n × Msg)

/-- Iterate a randomized step `k` times. -/
def iterM {α : Type} (f : α → PMF α) : ℕ → α → PMF α
  | 0, a => PMF.pure a
  | k + 1, a => (f a).bind (iterM f k)

/-- Is the party a client? -/
def Party.isClient {n : ℕ} : Party n → Bool
  | .server _ => false
  | _ => true

/-- The client corrupted in a configuration, if any. -/
def corruptedClient {n : ℕ} {S : Type} (c : Config n S) : Option Client :=
  if (Party.alice : Party n) ∈ c.corrupted then some .alice
  else if (Party.bob : Party n) ∈ c.corrupted then some .bob else none

/-- Total bit communication: the sum of the message lengths, each message counting at
least one bit. -/
def bitsUsed {n : ℕ} {S : Type} (c : Config n S) : ℕ :=
  (c.log.map (fun e => max 1 e.2.2.2.length)).sum

/-- Message complexity: the number of messages sent. -/
def msgsUsed {n : ℕ} {S : Type} (c : Config n S) : ℕ := c.log.length

/-- All parties in a fixed public order: Alice, Bob, servers `0, …, n-1`. -/
def allParties (n : ℕ) : List (Party n) :=
  .alice :: .bob :: (List.finRange n).map Party.server

namespace Protocol

variable {n : ℕ} {IA IB OA OB : Type} (pr : Protocol n IA IB OA OB)

/-- The oldest pending message addressed to `p`, with the remaining in-flight list. -/
def takeMsg (l : List (Party n × Party n × Msg)) (p : Party n) :
    Option ((Party n × Msg) × List (Party n × Party n × Msg)) :=
  match l.find? (fun e => decide (e.2.1 = p)) with
  | none => none
  | some e => some ((e.1, e.2.2), l.erase e)

/-- Party `p` performs its next local operation (if any). -/
def doAct (c : Config n pr.S) (p : Party n) : PMF (Config n pr.S) :=
  match pr.act p c.round (c.st p) with
  | none => PMF.pure c
  | some (.send dst m s') =>
      let m := wireMsg m
      PMF.pure { c with
        st := Function.update c.st p s'
        inflight := c.inflight ++ [(p, dst, m)]
        log := c.log ++ [(c.round, p, dst, m)]
        hist := if p ∈ c.corrupted then c.hist ++ [.sent p dst m s'] else c.hist }
  | some (.compute k) =>
      k.bind fun s' => PMF.pure { c with
        st := Function.update c.st p s'
        hist := if p ∈ c.corrupted then c.hist ++ [.computed p s'] else c.hist }

  | some (.erase s') =>
      if c.inflight.any (fun e => decide (e.1 = p)) then PMF.pure c
      else PMF.pure { c with
        st := Function.update c.st p s'
        hist := if p ∈ c.corrupted then c.hist ++ [.computed p s'] else c.hist }

/-- Deliver a selected private channel's oldest message. This permits all arrival
orders between different senders, without disclosing whether an honest channel is empty. -/
def doRecvFrom (c : Config n pr.S) (p fr : Party n) : PMF (Config n pr.S) :=
  match c.inflight.find? (fun e => decide (e.1 = fr ∧ e.2.1 = p)) with
  | none => PMF.pure c
  | some e =>
    let s' := pr.recv p c.round (c.st p) fr e.2.2
    PMF.pure { c with
      st := Function.update c.st p s'
      inflight := c.inflight.erase e
      hist := if p ∈ c.corrupted then c.hist ++ [.received p fr e.2.2 s'] else c.hist }

/-- Party `p` receives its oldest pending message (if any). -/
def doRecv (c : Config n pr.S) (p : Party n) : PMF (Config n pr.S) :=
  match takeMsg c.inflight p with
  | none => PMF.pure c
  | some ((fr, m), rest) =>
      let s' := pr.recv p c.round (c.st p) fr m
      PMF.pure { c with
        st := Function.update c.st p s'
        inflight := rest
        hist := if p ∈ c.corrupted then c.hist ++ [.received p fr m s'] else c.hist }

/-- Corrupting `p` is allowed when `p` is honest and the budget (at most one client and at
most `t` servers over the whole execution) permits it. -/
def mayCorrupt (t : ℕ) (c : Config n pr.S) (p : Party n) : Bool :=
  decide (p ∉ c.corrupted) &&
    (if p.isClient then decide (∀ q ∈ c.corrupted, q.isClient = false)
     else decide ((c.corrupted.filter (fun q => !q.isClient)).length < t))

/-- Corrupt `p`: the adversary receives its current (unerased) state. -/
def doCorrupt (t : ℕ) (c : Config n pr.S) (p : Party n) : PMF (Config n pr.S) :=
  if pr.mayCorrupt t c p then
    PMF.pure { c with corrupted := c.corrupted ++ [p], hist := c.hist ++ [.reveal p (c.st p)] }
  else PMF.pure c

/-- Apply one decision. -/
def applyDecision (t : ℕ) (c : Config n pr.S) : Decision n → PMF (Config n pr.S)
  | .act p => pr.doAct c p
  | .recv p => pr.doRecv c p
  | .recvFrom p fr => pr.doRecvFrom c p fr
  | .corrupt p => pr.doCorrupt t c p
  | .pass => PMF.pure c

/-- One adversarial step: the adversary picks a decision from its view, which is recorded
in its view, and the decision is applied. -/
def advStep {Aux : Type} (t : ℕ) (A : Adversary n pr.S Aux) (aux : Aux) (c : Config n pr.S) :
    PMF (Config n pr.S) :=
  (A.strat aux c.hist).bind fun d =>
    pr.applyDecision t { c with hist := c.hist ++ [.decided d] } d

/-- One forced pass at the round deadline: in the public order, each party receives a
pending message if it has one and otherwise performs its next operation. -/
def forcedPass (c : Config n pr.S) : PMF (Config n pr.S) :=
  (allParties n).foldlM (fun c p =>
    if (takeMsg c.inflight p).isSome then pr.doRecv c p else pr.doAct c p) c

/-- One synchronous round: `A.slots` adversarial scheduling/corruption decisions, then the
round deadline: all remaining operations and deliveries of the round are completed
(`opBound` forced passes) and the public clock advances. -/
def runRound {Aux : Type} (t : ℕ) (A : Adversary n pr.S Aux) (aux : Aux) (c : Config n pr.S) :
    PMF (Config n pr.S) :=
  (iterM (pr.advStep t A aux) A.slots c).bind fun c =>
    (iterM pr.forcedPass pr.opBound c).bind fun c =>
      PMF.pure { c with round := c.round + 1, hist := c.hist ++ [.roundEnd c.round] }

/-- After the last round the adversary may still corrupt parties (`A.slots` more
decisions; only corruptions have an effect). -/
def finalStep {Aux : Type} (t : ℕ) (A : Adversary n pr.S Aux) (aux : Aux)
    (c : Config n pr.S) : PMF (Config n pr.S) :=
  (A.strat aux c.hist).bind fun d =>
    let c := { c with hist := c.hist ++ [.decided d] }
    match d with
    | .corrupt p => pr.doCorrupt t c p
    | _ => PMF.pure c

/-- Initial configuration on inputs `a`, `b`. If `fixed = some P`, client `P` is corrupted
from the start and its initial state is revealed (the fixed-client setting of
Sections 4–8); otherwise nobody is corrupted initially (adaptive setting). -/
def initConfig (a : IA) (b : IB) (fixed : Option Client) : Config n pr.S :=
  let st : Party n → pr.S := fun p =>
    match p with
    | .alice => pr.initA a
    | .bob => pr.initB b
    | .server i => pr.initS i
  match fixed with
  | none => { st := st, inflight := [], corrupted := [], round := 0, hist := [], log := [] }
  | some P => { st := st, inflight := [], corrupted := [P.toParty],
                round := 0, hist := [.reveal P.toParty (st P.toParty)], log := [] }

/-- The real execution against adversary `A` with server budget `t`: the distribution of
the final configuration. -/
def realExec {Aux : Type} (t : ℕ) (A : Adversary n pr.S Aux) (aux : Aux) (a : IA) (b : IB)
    (fixed : Option Client) : PMF (Config n pr.S) :=
  (iterM (pr.runRound t A aux) pr.rounds (pr.initConfig a b fixed)).bind
    (iterM (pr.finalStep t A aux) A.slots)

/-- The protocol aborted: some client output `⊥`. -/
def aborted (c : Config n pr.S) : Prop :=
  pr.outA (c.st .alice) = none ∨ pr.outB (c.st .bob) = none

/-- The operational bound really completes each synchronous round. This is a
well-formedness condition on an abstract protocol, not a security assumption. -/
def Synchronous : Prop :=
  ∀ (Aux : Type) (A : Adversary n pr.S Aux) (aux : Aux) (t : ℕ)
    (a : IA) (b : IB) (fixed : Option Client) (r : ℕ), r < pr.rounds →
    ∀ cfg ∈ (iterM (pr.runRound t A aux) r (pr.initConfig a b fixed)).support,
      ∀ scheduled ∈ (iterM (pr.advStep t A aux) A.slots cfg).support,
      ∀ done ∈ (iterM pr.forcedPass pr.opBound scheduled).support,
        done.inflight = [] ∧ ∀ p, pr.act p r (done.st p) = none

end Protocol

end ChoiSemiHonestMPC.OTUpper


