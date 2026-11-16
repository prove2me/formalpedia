-- Prove2me | Definitions.Def_DistributedMWC440_UpperBound_Supplement_BCC
-- name    : DistributedMWC440_UpperBound_Supplement_BCC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:49:23.252322+00:00
-- url     : https://prove2.me/theorems/456a532f-8a85-4b0b-a398-0321848692ed
-- title:
--   The broadcast congested clique model, its computable protocols, and Theorem 4's claim
-- statement:
--   In the **broadcast congested clique** the input is a graph $G$ on $\mathrm{Fin}\,n$, not required to be connected, while the communication network is the complete graph. In each synchronous round every node computes locally and broadcasts one message of $O(\log n)$ bits (a payload below $(\max(2,n))^B$) or stays silent; every other node receives it labelled with the sender's ID. Each node initially knows $n$, its own ID and, for each incident edge, the neighbour's ID and the edge weight (undirected weighted inputs, positive integer weights at most $n^q$) or the arc directions (directed unweighted inputs, loopless digraphs). Private fair random bits are drawn as in the base mission.
--
--   The output convention is that of Definition 1.1: all nodes know the actual weight of one common simple cycle $C$ with $w(C)\le\alpha\cdot\mathrm{OPT}$, and both endpoints of every edge know whether it belongs to $C$; on an acyclic input, the common no-cycle output.
--
--   Two algorithm classes are defined. General algorithms are arbitrary $n$-dependent state machines (used by the lower bound, Theorem 5, together with the notion of solving with high probability within $T(n)$ rounds). Protocols are computable and uniform in $n$ (used by the upper bound, Theorem 4). The proposition `BCCTradeoff q b` is Theorem 4's claim: for every confidence exponent there are a message exponent and constants $C>0$, $p$, uniform in real $k\ge1$, and for each $k$ a protocol, such that on every input with $n\ge\max(2,n_0)$ nodes every broadcast respects the width bound, and with probability at least $1-n^{-\text{confidence}}$ the protocol halts within $C(\log n)^p n^{1/k}$ rounds with a correct $(k+1)$-approximate output.
--
--   **Formalization Note** Neighbourhoods and inboxes are presented as increasing lists of the codes $\mathrm{pair}(\text{ID},\text{label})$, so the hidden vertex indexing is never revealed. Knowledge of neighbour IDs is the standard clique convention of [DKO14]; without it a node could not identify its input edges.
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), §1.2, printed p. 6 / PDF p. 8 (Theorems 4, 5); §3, printed p. 13 / PDF p. 15 (model); Definition 1.1, printed pp. 1–2 / PDF pp. 3–4; proof of Theorem 4, printed p. 30 / PDF p. 32.

import Definitions.Def_DistributedMWC440_UpperBound_Supplement_CongestLB

open scoped ENNReal
open MeasureTheory Classical

noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-!
The broadcast congested clique model of Chang et al., STOC 2027 submission #440 (§1.2, printed
p. 6 / PDF p. 8; §3, printed p. 13 / PDF p. 15): the input graph `G` on `Fin n` need not be
connected; the communication network is the complete graph; in each synchronous round every node
computes locally and broadcasts one `O(log n)`-bit message (or stays silent), received by every
other node labelled with the sender's ID. Each node initially knows `n`, its own ID and, for each
incident edge, the neighbour's ID and the edge weight (resp. the arc directions) — the standard
clique knowledge of [DKO14]. Private fair random bits as in the base `tapeLaw`.

`BCCAlg` is the general class (arbitrary, `n`-dependent state machines; used by the lower bound,
Theorem 5); `BCCProtocol` is the computable uniform class of the upper bound (Theorem 4).
-/

/-- A general broadcast-congested-clique algorithm. `initial n (id, nbrs)`: initial state from the
node's ID and the increasing list of codes `Nat.pair (neighbour ID) (edge label)` of its incident
edges. `send n s`: the broadcast. The inbox is the increasing list of codes
`Nat.pair (sender ID) (encOpt message)` of all other nodes. `mark n s i` is the output code for
the incident edge to the neighbour with ID `i`. -/
structure BCCAlg where
  initial : ℕ → ℕ × List ℕ → ℕ
  send : ℕ → ℕ → Option ℕ
  bitCount : ℕ → ℕ × List ℕ → ℕ
  step : ℕ → ℕ × List ℕ × List Bool → ℕ
  halt : ℕ → ℕ → Bool
  value : ℕ → ℕ → Option ℕ
  mark : ℕ → ℕ → ℕ → ℕ

/-- Silence is `0`, the payload `m` is `m + 1`. -/
def encOpt : Option ℕ → ℕ
  | none => 0
  | some m => m + 1

/-- Execution on `n` nodes with IDs `id` and initial neighbourhood lists `init`. -/
def bccState (n : ℕ) (A : BCCAlg) (id : Fin n → ℕ) (init : Fin n → List ℕ) (ω : Tapes n) :
    ℕ → Fin n → ℕ
  | 0, v => A.initial n (id v, init v)
  | t + 1, v =>
    let s := bccState n A id init ω t
    if A.halt n (s v) then s v else
      let inbox := Finset.sort
        ((Finset.univ.filter (fun u => u ≠ v)).image
          (fun u => Nat.pair (id u) (encOpt (A.send n (s u)))))
      let bits := List.ofFn (fun j : Fin (A.bitCount n (s v, inbox)) => ω (v, t, j.val))
      A.step n (s v, inbox, bits)

def BHalted (n : ℕ) (A : BCCAlg) (id : Fin n → ℕ) (init : Fin n → List ℕ) (ω : Tapes n)
    (t : ℕ) : Prop :=
  ∀ v, A.halt n (bccState n A id init ω t v) = true

/-- Every broadcast before round `t` is below `(max 2 n)^B`; halted nodes are silent. -/
def BWidth (n : ℕ) (A : BCCAlg) (id : Fin n → ℕ) (init : Fin n → List ℕ) (B : ℕ)
    (ω : Tapes n) (t : ℕ) : Prop :=
  ∀ r < t, ∀ v, ∀ m, A.send n (bccState n A id init ω r v) = some m →
    m < (max 2 n) ^ B ∧ A.halt n (bccState n A id init ω r v) = false

/-! ### Undirected weighted inputs -/

/-- An undirected input graph on `Fin n` (connectivity not required) with positive integer weights
at most `n^q` and distinct IDs below `(max 2 n)^b`. -/
structure BCCInstance (n q b : ℕ) where
  W : WGraph (Fin n)
  weight : Fin n → Fin n → ℕ
  weight_eq : ∀ u v, W.graph.Adj u v → W.length u v = (weight u v : ℝ)
  weight_pos : ∀ u v, W.graph.Adj u v → 0 < weight u v
  weight_bound : ∀ u v, W.graph.Adj u v → weight u v ≤ n ^ q
  id : Fin n → ℕ
  id_injective : Function.Injective id
  id_bound : ∀ v, id v < (max 2 n) ^ b

def BCCInstance.init {n q b : ℕ} (I : BCCInstance n q b) (v : Fin n) : List ℕ :=
  Finset.sort
    ((Finset.univ.filter (fun u => I.W.graph.Adj v u)).image
      (fun u => Nat.pair (I.id u) (I.weight v u)))

/-- Output convention of Definition 1.1, in the clique: the common actual weight of one simple cycle
`C` with `w(C) ≤ ratio · OPT` at every node, and a nonzero mark for exactly the incident edges of
`C` at both endpoints; on an acyclic input the common no-cycle output. -/
def BWCorrect {n q b : ℕ} (I : BCCInstance n q b) (A : BCCAlg) (ω : Tapes n) (t : ℕ)
    (ratio : ℝ) : Prop :=
  let s := bccState n A I.id I.init ω t
  (∃ C : Cycle I.W, ENNReal.ofReal C.weight ≤ ENNReal.ofReal ratio * optimum I.W ∧
    ∀ v, (A.value n (s v)).map (fun a => (a : ℝ)) = some C.weight ∧
      ∀ u, I.W.graph.Adj v u → (A.mark n (s v) (I.id u) ≠ 0 ↔ s(v, u) ∈ C.walk.edges)) ∨
  (IsEmpty (Cycle I.W) ∧ ∀ v, A.value n (s v) = none ∧
    ∀ u, I.W.graph.Adj v u → A.mark n (s v) (I.id u) = 0)

def BWEvent {n q b : ℕ} (I : BCCInstance n q b) (A : BCCAlg) (B : ℕ) (ratio budget : ℝ) :
    Set (Tapes n) :=
  {ω | ∃ t : ℕ, (t : ℝ) ≤ budget ∧ BHalted n A I.id I.init ω t ∧
    BWidth n A I.id I.init B ω t ∧ BWCorrect I A ω t ratio}

/-- `A` solves `α(n)`-Apx-MWC on undirected weighted inputs in the broadcast congested clique with
high probability within `T(n)` rounds. -/
def SolvesBCCWeighted (A : BCCAlg) (α : ℕ → ℝ) (q b B : ℕ) (T : ℕ → ℕ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ I : BCCInstance n q b,
    ENNReal.ofReal (1 - (n : ℝ) ^ (-c')) ≤ tapeLaw n (BWEvent I A B (α n) (T n))

/-! ### Directed unweighted inputs -/

/-- A loopless digraph on `Fin n` (antiparallel arcs allowed, connectivity not required) with
distinct IDs below `(max 2 n)^b`. -/
structure DBCCInstance (n b : ℕ) where
  D : Digraph (Fin n)
  loopless : ∀ v, ¬ D.Adj v v
  id : Fin n → ℕ
  id_injective : Function.Injective id
  id_bound : ∀ v, id v < (max 2 n) ^ b

def DBCCInstance.init {n b : ℕ} (I : DBCCInstance n b) (v : Fin n) : List ℕ :=
  Finset.sort
    ((Finset.univ.filter (fun u => (commGraph I.D).Adj v u)).image
      (fun u => Nat.pair (I.id u) (dirCode I.D v u)))

def BDCorrect {n b : ℕ} (I : DBCCInstance n b) (A : BCCAlg) (ω : Tapes n) (t : ℕ)
    (ratio : ℝ) : Prop :=
  let s := bccState n A I.id I.init ω t
  (∃ C : DCycle I.D, (C.len : ℝ≥0∞) ≤ ENNReal.ofReal ratio * dOptimum I.D ∧
    ∀ v, A.value n (s v) = some C.len ∧
      ∀ u, (commGraph I.D).Adj v u →
        (((A.mark n (s v) (I.id u)).testBit 0 = true ↔ C.HasArc v u) ∧
         ((A.mark n (s v) (I.id u)).testBit 1 = true ↔ C.HasArc u v))) ∨
  (IsEmpty (DCycle I.D) ∧ ∀ v, A.value n (s v) = none ∧
    ∀ u, (commGraph I.D).Adj v u → A.mark n (s v) (I.id u) = 0)

def BDEvent {n b : ℕ} (I : DBCCInstance n b) (A : BCCAlg) (B : ℕ) (ratio budget : ℝ) :
    Set (Tapes n) :=
  {ω | ∃ t : ℕ, (t : ℝ) ≤ budget ∧ BHalted n A I.id I.init ω t ∧
    BWidth n A I.id I.init B ω t ∧ BDCorrect I A ω t ratio}

def SolvesBCCDirected (A : BCCAlg) (α : ℕ → ℝ) (b B : ℕ) (T : ℕ → ℕ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ I : DBCCInstance n b,
    ENNReal.ofReal (1 - (n : ℝ) ^ (-c')) ≤ tapeLaw n (BDEvent I A B (α n) (T n))

/-! ### The computable class of the upper bound -/

/-- A uniform computable broadcast-congested-clique protocol (the same program for every `n`,
which it receives as input). -/
structure BCCProtocol where
  initial : ℕ × ℕ × List ℕ → ℕ
  send : ℕ → Option ℕ
  bitCount : ℕ × List ℕ → ℕ
  step : ℕ × List ℕ × List Bool → ℕ
  halt : ℕ → Bool
  value : ℕ → Option ℕ
  mark : ℕ × ℕ → ℕ
  initial_computable : Computable initial
  send_computable : Computable send
  bitCount_computable : Computable bitCount
  step_computable : Computable step
  halt_computable : Computable halt
  value_computable : Computable value
  mark_computable : Computable mark

def BCCProtocol.toAlg (P : BCCProtocol) : BCCAlg where
  initial n x := P.initial (n, x)
  send _ := P.send
  bitCount _ := P.bitCount
  step _ := P.step
  halt _ := P.halt
  value _ := P.value
  mark _ s i := P.mark (s, i)

/-- Theorem 4's claim for weight exponent `q` and ID exponent `b`, quantified exactly as the base
`Tradeoff`: for every confidence exponent, one message exponent and one soft-O constant pair, uniform
in real `k ≥ 1`, and for each `k` one protocol, such that on every input of size `n ≥ max 2 n₀`
every broadcast respects the width bound on every execution and, with probability at least
`1 - n^(-confidence)`, the protocol halts within `C (log n)^p n^(1/k)` rounds with a correct
`(k+1)`-approximate output. -/
def BCCTradeoff (q b : ℕ) : Prop :=
  ∀ confidence : ℝ, 0 < confidence →
  ∃ (B p n₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ k : ℝ, 1 ≤ k →
    ∃ P : BCCProtocol, ∀ n ≥ max 2 n₀, ∀ I : BCCInstance n q b,
      (∀ ω t, BWidth n P.toAlg I.id I.init B ω t) ∧
      (let budget := C * (Real.log n) ^ p * (n : ℝ) ^ (1 / k)
       MeasurableSet (BWEvent I P.toAlg B (k + 1) budget) ∧
       ENNReal.ofReal (1 - (n : ℝ) ^ (-confidence)) ≤
         tapeLaw n (BWEvent I P.toAlg B (k + 1) budget))

end DistributedMWC440.UpperBound.Supplement


