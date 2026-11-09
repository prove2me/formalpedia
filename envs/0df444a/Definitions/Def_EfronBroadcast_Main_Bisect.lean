-- Prove2me | Definitions.Def_EfronBroadcast_Main_Bisect
-- name    : EfronBroadcast_Main_Bisect
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:26.519207+00:00
-- url     : https://prove2.me/theorems/0cc5a12b-5ff3-408a-99f5-0c2c380020f3
-- title:
--   Operational Bisect and sent-bit accounting
-- statement:
--   There are $n$ physical parties, a designated receiver $q$, an initial set $A\subseteq[n]$, an ordered set $P$ of senders, and private sets $W_p\subseteq[n]$. A corruption-time map specifies when each party is permanently corrupted, or that it is never corrupted. At most $t$ parties may ever be corrupted. Correct means never corrupted.
--
--   The independent SPLIT input condition is
--
--   $$
--   |P|\le |W_p|-|A|\qquad\text{for each correct sender }p\in P.
--   $$
--
--   Its output specification requires that, when $q$ is correct, non-bottom outputs are distinct and outside $A$, and each correct sender $p$ receives an output in $W_p\setminus A$.
--
--   The interval tree divides $[n]$ into lower and upper halves. Bisect starts every sender at the root. At each of $k$ layers, a correct sender follows only a child-node message and sends its actual two child counts. The receiver rejects missing, oversized, or inconsistent reports, orders survivors by decreasing left count with the input order breaking ties, and performs the printed left/right counter update. Each layer records both rounds' actual sent messages. Correct actions use their own state, inputs and incoming messages; Byzantine actions may omit messages, send malformed packets, equivocate, and overwrite corrupted states based on the past.
--
--   $$
--   \operatorname{rounds}(H)=2|H|,\qquad
--   \operatorname{bits}(H)=\sum_{\text{actual packets in }H}|\operatorname{encode}(\text{packet})|.
--   $$
--
--   This definition contains no assumed invariant, correctness, or resource bound. The local transition functions are stated for an arbitrary sender identity type, because Ladder runs them on virtual senders $(p,e)$; the execution model here is the one for physical senders, including $n=1$, where $k=0$ and no messages are sent.
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 12, PDF p. 13, Protocol 4; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Splitting
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Binary interval tree, with lower half on `false` and upper half on `true`. -/
noncomputable def interval {n : ℕ} (σ : List Bool) : Finset (Fin n) :=
  σ.foldl (fun I b =>
    let lo := (I.toList.mergeSort (fun x y => x.val ≤ y.val)).take (I.card / 2)
    if b then I \ lo.toFinset else lo.toFinset) Finset.univ

/-- Protocol 4's typed messages, with an arbitrary malformed packet case. -/
inductive BisectMessage where
  | node (σ : List Bool)
  | count (left right : ℕ)
  | malformed (bytes : List Bool)
  deriving DecidableEq, Inhabited

/-- An explicit self-delimiting integer encoding; zero also has an encoding. -/
def encodeNat (v : ℕ) : List Bool :=
  let bits := (Nat.digits 2 v).map (fun b => b == 1)
  List.replicate bits.length true ++ [false] ++ bits

/-- Actual serialized payloads, including a two-bit type tag. -/
def BisectMessage.encode : BisectMessage → List Bool
  | .node σ => [false, false] ++ encodeNat σ.length ++ σ
  | .count l r => [false, true] ++ encodeNat l ++ encodeNat r
  | .malformed bytes => [true, true] ++ bytes

def packetBits (messages : List BisectMessage) : ℕ :=
  (messages.map (fun m => m.encode.length)).sum

/-- The receiver's operational local state, for senders of an arbitrary identity type `X`
(physical parties, or the virtual senders `(p, e)` of Ladder). No invariant or correctness
proof is a field. -/
structure BisectReceiver (X : Type) where
  F : Finset X
  node : X → List Bool
  weight : X → ℕ

def initialReceiver {N : ℕ} {X : Type} (A : Finset (Fin N)) (P : List X) :
    BisectReceiver X := ⟨∅, fun _ => [], fun _ => A.card + P.length⟩

def firstCount (messages : List BisectMessage) : Option (ℕ × ℕ) :=
  messages.findSome? (fun m => match m with
    | .count l r => some (l, r)
    | _ => none)

/-- Sender follows only a child of its current node (Protocol 4, line 4). -/
def senderNode (σ : List Bool) (messages : List BisectMessage) : List Bool :=
  ((messages.findSome? (fun m => match m with
    | .node τ => if τ = σ ++ [false] ∨ τ = σ ++ [true] then some τ else none
    | _ => none)).getD σ)

noncomputable def honestCount {n : ℕ} (W : Finset (Fin n)) (σ : List Bool) : BisectMessage :=
  .count ((interval (σ ++ [false])) ∩ W).card ((interval (σ ++ [true])) ∩ W).card

/-- The receiver rejects missing or inconsistent counts before making assignments;
`N` is the size of the value universe. -/
noncomputable def rejectCounts {X : Type} [DecidableEq X] (N h : ℕ) (P : List X)
    (S : BisectReceiver X) (messages : X → List BisectMessage) : Finset X := by
  classical
  exact S.F ∪ P.toFinset.filter (fun x => match firstCount (messages x) with
    | none => True
    | some (l, r) => N / 2 ^ h < l ∨ N / 2 ^ h < r ∨ l + r < S.weight x)

/-- Protocol 4, lines 18--22. Processing distinct parent nodes can be interleaved:
each node has its own `z`; within it left counts decrease, with input-list tie order. -/
noncomputable def receiverMove {N : ℕ} {X : Type} [DecidableEq X] (h : ℕ) (A : Finset (Fin N))
    (P : List X) (S : BisectReceiver X)
    (messages : X → List BisectMessage) : BisectReceiver X := by
  classical
  let F := rejectCounts N h P S messages
  let counts := fun x => (firstCount (messages x)).getD (0, 0)
  let order := (P.filter (fun x => x ∉ F)).mergeSort (fun x y =>
    (counts x).1 > (counts y).1 ∨
      ((counts x).1 = (counts y).1 ∧ P.idxOf x ≤ P.idxOf y))
  let z₀ := fun σ : List Bool => ((interval (σ ++ [false])) ∩ A).card
  let start : BisectReceiver X × (List Bool → ℕ) := (⟨F, S.node, S.weight⟩, z₀)
  exact (order.foldl (fun (st : BisectReceiver X × (List Bool → ℕ)) x =>
    let σ := S.node x
    let l := (counts x).1
    let r := (counts x).2
    let goLeft := decide (st.2 σ < l)
    let node' := σ ++ [!goLeft]
    let w' := if goLeft then l else r
    let z' := if goLeft then Function.update st.2 σ (st.2 σ + 1) else st.2
    (⟨F, Function.update st.1.node x node', Function.update st.1.weight x w'⟩, z')) start).1

/-- Protocol 4, line 24: the leaf index of a surviving sender, `none` (⊥) otherwise. -/
noncomputable def leafOutput {N : ℕ} {X : Type} [DecidableEq X] (P : List X)
    (S : BisectReceiver X) (x : X) : Option (Fin N) := by
  classical
  exact if x ∈ P ∧ x ∉ S.F then (interval (S.node x)).toList.head? else none

/-- A trace state includes both roles' local nodes, and the previous received node messages. -/
structure BisectSnapshot (n : ℕ) where
  receiver : BisectReceiver (Party n)
  sender : Party n → List Bool
  inbox : Party n → List BisectMessage

/-- Actual sends in one two-round layer. Endpoints are the designated receiver and
the sender indexing each list. Multiple messages, omission and malformed data are allowed. -/
structure BisectLayer (n : ℕ) where
  counts : Party n → List BisectMessage
  nodes : Party n → List BisectMessage
  after : BisectSnapshot n

/-- A Byzantine strategy chooses arbitrary messages and overwritten corrupted states.
The finite past is supplied explicitly; choices may depend on the execution state.
No correctness or cost property is assumed of this strategy. -/
structure BisectAdversary (n : ℕ) where
  corruptions : Corruptions n
  senderOverwrite : ℕ → List (BisectLayer n) → BisectSnapshot n → Party n → List Bool
  counts : ℕ → List (BisectLayer n) → BisectSnapshot n → Party n → List BisectMessage
  receiverOverwrite : ℕ → List (BisectLayer n) → BisectSnapshot n →
    (Party n → List BisectMessage) → BisectReceiver (Party n)
  nodes : ℕ → List (BisectLayer n) → BisectSnapshot n →
    (Party n → List BisectMessage) → Party n → List BisectMessage

/-- The no-corruption strategy is an explicit inhabitant, including empty malformed channels. -/
def silentAdversary (n : ℕ) : BisectAdversary n where
  corruptions := fun _ => none
  senderOverwrite := fun _ _ s p => s.sender p
  counts := fun _ _ _ _ => []
  receiverOverwrite := fun _ _ s _ => s.receiver
  nodes := fun _ _ _ _ _ => []

/-- One actual two-round transition, with corruptions at the beginning of either round.
Correct role actions depend only on their own inputs, local state and delivered messages. -/
noncomputable def bisectLayer {n : ℕ} (k h : ℕ) (q : Party n)
    (A : Finset (Fin n)) (P : List (Party n)) (W : Party n → Finset (Fin n))
    (adv : BisectAdversary n) (past : List (BisectLayer n))
    (before : BisectSnapshot n) : BisectLayer n := by
  classical
  let σ := fun p => if IsCorruptAt adv.corruptions (2 * h + 1) p then
    adv.senderOverwrite h past before p else senderNode (before.sender p) (before.inbox p)
  let counts := fun p => if p ∉ P then [] else
    if IsCorruptAt adv.corruptions (2 * h + 1) p then adv.counts h past before p
    else [honestCount (W p) (σ p)]
  let receiver := if IsCorruptAt adv.corruptions (2 * h + 2) q then
    adv.receiverOverwrite h past before counts else receiverMove (h + 1) A P before.receiver counts
  let nodes := fun p => if IsCorruptAt adv.corruptions (2 * h + 2) q then
    adv.nodes h past before counts p
    else if h + 1 < k ∧ p ∈ P ∧ p ∉ receiver.F then [.node (receiver.node p)] else []
  exact ⟨counts, nodes, ⟨receiver, σ, nodes⟩⟩

/-- Run exactly `layers` two-round steps. The intended completed execution has `layers = k`.
The stored history is the complete list of actual sends, not a resource certificate. -/
noncomputable def bisectHistory {n : ℕ} (k : ℕ) (q : Party n) (A : Finset (Fin n))
    (P : List (Party n)) (W : Party n → Finset (Fin n)) (adv : BisectAdversary n) :
    ℕ → List (BisectLayer n)
  | 0 => []
  | h + 1 =>
    let past := bisectHistory k q A P W adv h
    let initial : BisectSnapshot n := ⟨initialReceiver A P, fun _ => [], fun _ => []⟩
    let before := (past.getLast?).map BisectLayer.after |>.getD initial
    past ++ [bisectLayer k h q A P W adv past before]

noncomputable def bisectState {n : ℕ} (k : ℕ) (q : Party n) (A : Finset (Fin n))
    (P : List (Party n)) (W : Party n → Finset (Fin n)) (adv : BisectAdversary n)
    (h : ℕ) : BisectReceiver (Party n) :=
  ((bisectHistory k q A P W adv h).getLast?).map (fun l => l.after.receiver) |>.getD
    (initialReceiver A P)

/-- Leaf output is computed from the final local receiver state. -/
noncomputable def bisectOutput {n : ℕ} (k : ℕ) (q : Party n) (A : Finset (Fin n))
    (P : List (Party n)) (W : Party n → Finset (Fin n)) (adv : BisectAdversary n)
    (p : Party n) : Option (Fin n) := by
  classical
  let S := bisectState k q A P W adv k
  exact leafOutput P S p

/-- A role's actual sent bits, counting every receiver/sender copy in the stored history. -/
noncomputable def bisectReceiverBits {n : ℕ} (history : List (BisectLayer n)) : ℕ :=
  (history.map (fun l => ∑ p : Party n, packetBits (l.nodes p))).sum

def bisectSenderBits {n : ℕ} (history : List (BisectLayer n)) (p : Party n) : ℕ :=
  (history.map (fun l => packetBits (l.counts p))).sum

def bisectRounds {n : ℕ} (history : List (BisectLayer n)) : ℕ := 2 * history.length


end EfronBroadcast.Main


