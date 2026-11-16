-- Prove2me | Definitions.Def_DistributedMWC440_UpperBound_Supplement_CongestLB
-- name    : DistributedMWC440_UpperBound_Supplement_CongestLB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:48:43.23459+00:00
-- url     : https://prove2.me/theorems/4c835142-36f8-4a6a-83f0-b211dcffef56
-- title:
--   CONGEST executions of general algorithms on weighted and directed networks
-- statement:
--   This file fixes the CONGEST model of §3 for the lower bound of Theorem 2, in two input classes.
--
--   1. **Algorithms.** A general algorithm is, for each network size $n$, an arbitrary state machine (not necessarily computable) with natural-number states. A node starts from $n$, its own ID and, for each port, the neighbour's ID and the local edge label. In each synchronous round it sends one optional message per port, draws a number of fresh private fair bits, and moves to a new state from its state, its per-port inbox and those bits; a halted node keeps its state. The output is a value (the cycle weight) and a mark per port. Every computable protocol of the base mission is such an algorithm, with an identical execution.
--   2. **Undirected weighted networks** are the base mission's networks: connected simple graphs on $\mathrm{Fin}\,n$ with positive integer weights at most $n^q$, distinct IDs below $(\max(2,n))^b$, and private port orders.
--   3. **Directed unweighted networks** are loopless digraphs on $\mathrm{Fin}\,n$ (antiparallel arcs allowed) whose underlying undirected graph is connected and carries the bidirectional links; each port's label records the directions of the arcs on that link.
--   4. **Output (Definition 1.1).** All nodes know the actual weight $w(C)$ of one common simple cycle $C$ with $w(C)\le\alpha\cdot\mathrm{OPT}$, and both endpoints of every edge know whether it belongs to $C$ (in the directed case, separately for each of the two possible arcs). On an acyclic input, the common no-cycle output.
--   5. **Solving with high probability within $T(n)$ rounds** means: for some $c'>0$ and all sufficiently large $n$, on every network of size $n$, with probability at least $1-n^{-c'}$ the algorithm halts by round $T(n)$, every message sent so far is below $(\max(2,n))^B$, and the output is correct.
--
--   **Formalization Note** The randomness is the base mission's tape law: one independent fair bit per node, round and within-round index. The width bound is required only along successful executions, which enlarges the algorithm class and so strengthens a lower bound.
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), §1, printed pp. 1–2 / PDF pp. 3–4 (Definition 1.1 and output convention); §3, printed p. 13 / PDF p. 15 (CONGEST model); Theorem 2, printed p. 4 / PDF p. 6.

import Definitions.Def_DistributedMWC440_UpperBound_CONGEST
import Definitions.Def_DistributedMWC440_UpperBound_Supplement_Directed

open scoped ENNReal
open MeasureTheory Classical

noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-!
The CONGEST model of Chang et al., STOC 2027 submission #440 (§3, printed p. 13 / PDF p. 15), with
the algorithm class over which the lower bound (Theorem 2, printed p. 4 / PDF p. 6) quantifies,
for undirected weighted and for directed unweighted inputs. The output convention is the one after
Definition 1.1 (printed pp. 1–2 / PDF pp. 3–4).

The class `LocalAlg` is larger than the base mission's computable `Protocol`: for each network
size `n` an arbitrary (not necessarily computable) state machine that knows `n`, its own ID and,
per port, the neighbour's ID and the local edge label. Every base `Protocol` is a `LocalAlg`
through `ofProtocol`, and its execution below is the base `stateAtInput` with empty input.
-/

/-- A general distributed algorithm: states are natural numbers (any finite local information);
every function may depend arbitrarily on the network size `n` (its first argument).
`initial n (id, ports)`: the initial state from the node's own ID and, per port, the code
`Nat.pair (neighbour ID) (edge label)`. `send n s`: one optional message per port.
`bitCount`, `step`: the number of fresh private fair bits used in a round, and the new state from
the state, the per-port inbox and those bits. `value` and `mark n s p` are the output: the cycle
weight, and a code for the edge at port `p`. -/
structure LocalAlg where
  initial : ℕ → ℕ × List ℕ → ℕ
  send : ℕ → ℕ → List (Option ℕ)
  bitCount : ℕ → ℕ × List (Option ℕ) → ℕ
  step : ℕ → ℕ × List (Option ℕ) × List Bool → ℕ
  halt : ℕ → ℕ → Bool
  value : ℕ → ℕ → Option ℕ
  mark : ℕ → ℕ → ℕ → ℕ

/-- Every base-mission protocol (which ignores `n` and neighbour IDs) is a `LocalAlg`; its edge
mark is `1` for a marked port and `0` otherwise. -/
def ofProtocol (P : Protocol) : LocalAlg where
  initial _ x := P.initial ((x.1, x.2.map fun z => (Nat.unpair z).2), [])
  send _ := P.send
  bitCount _ := P.bitCount
  step _ := P.step
  halt _ := P.halt
  value _ := P.value
  mark _ s p := if (P.marks s)[p]?.getD false then 1 else 0

/-- A communication graph with a private port order at every node. -/
structure PortGraph (n : ℕ) where
  G : SimpleGraph (Fin n)
  ports : (v : Fin n) → Fin (G.neighborSet v).ncard ≃ G.neighborSet v

def PortGraph.deg {n : ℕ} (P : PortGraph n) (v : Fin n) : ℕ := (P.G.neighborSet v).ncard

def lsent (A : LocalAlg) (n state p : ℕ) : Option ℕ := (A.send n state)[p]?.join

/-- The per-port inbox of `v`: what each neighbour sends on its port towards `v`. -/
def lincoming {n : ℕ} (P : PortGraph n) (A : LocalAlg) (state : Fin n → ℕ) (v : Fin n) :
    List (Option ℕ) :=
  List.ofFn fun p : Fin (P.deg v) =>
    let u := P.ports v p
    let rev : P.G.neighborSet u.val := ⟨v, u.property.symm⟩
    lsent A n (state u.val) ((P.ports u.val).symm rev).val

/-- Synchronous execution: one independent fair bit per node, round and within-round index
(`ω (v, t, j)`, as in the base `tapeLaw`). A halted node keeps its state. -/
def lstate {n : ℕ} (P : PortGraph n) (A : LocalAlg) (init : Fin n → ℕ × List ℕ)
    (ω : Tapes n) : ℕ → Fin n → ℕ
  | 0, v => A.initial n (init v)
  | t + 1, v =>
    let state := lstate P A init ω t
    if A.halt n (state v) then state v else
      let inbox := lincoming P A state v
      let bits := List.ofFn (fun j : Fin (A.bitCount n (state v, inbox)) => ω (v, t, j.val))
      A.step n (state v, inbox, bits)

def LHalted {n : ℕ} (P : PortGraph n) (A : LocalAlg) (init : Fin n → ℕ × List ℕ)
    (ω : Tapes n) (t : ℕ) : Prop :=
  ∀ v, A.halt n (lstate P A init ω t v) = true

/-- Messages of `O(log n)` bits: every payload sent before round `t` is below `(max 2 n)^B`, and
halted nodes are silent. -/
def LWidth {n : ℕ} (P : PortGraph n) (A : LocalAlg) (init : Fin n → ℕ × List ℕ) (B : ℕ)
    (ω : Tapes n) (t : ℕ) : Prop :=
  ∀ r < t, ∀ v, ∀ p < P.deg v, ∀ m, lsent A n (lstate P A init ω r v) p = some m →
    m < (max 2 n) ^ B ∧ A.halt n (lstate P A init ω r v) = false

/-! ### Undirected weighted inputs: the base `Network` -/

def netPorts {n q b : ℕ} (I : Network n q b) : PortGraph n := ⟨I.W.graph, I.ports⟩

/-- Initial knowledge: own ID and, per port, the neighbour's ID and the edge weight. -/
def netInit {n q b : ℕ} (I : Network n q b) (v : Fin n) : ℕ × List ℕ :=
  (I.id v, List.ofFn fun p : Fin (degree I v) =>
    Nat.pair (I.id (I.ports v p).val) (I.weight v (I.ports v p).val))

/-- Output convention (Definition 1.1 and the paragraph after it): all nodes know the actual weight
of one common simple cycle `C` with `w(C) ≤ ratio · OPT`, and both endpoints of every edge know
whether it belongs to `C` (nonzero mark); on an acyclic input, the common no-cycle output. -/
def WCorrect {n q b : ℕ} (I : Network n q b) (A : LocalAlg) (ω : Tapes n) (t : ℕ)
    (ratio : ℝ) : Prop :=
  let s := lstate (netPorts I) A (netInit I) ω t
  (∃ C : Cycle I.W, ENNReal.ofReal C.weight ≤ ENNReal.ofReal ratio * optimum I.W ∧
    ∀ v, (A.value n (s v)).map (fun a => (a : ℝ)) = some C.weight ∧
      ∀ p : Fin (degree I v),
        (A.mark n (s v) p.val ≠ 0 ↔ s(v, (I.ports v p).val) ∈ C.walk.edges)) ∨
  (IsEmpty (Cycle I.W) ∧ ∀ v, A.value n (s v) = none ∧
    ∀ p < degree I v, A.mark n (s v) p = 0)

/-- Success by round `T`: halted, width-respecting, correct. -/
def WEvent {n q b : ℕ} (I : Network n q b) (A : LocalAlg) (B : ℕ) (ratio : ℝ) (T : ℕ) :
    Set (Tapes n) :=
  {ω | ∃ t ≤ T, LHalted (netPorts I) A (netInit I) ω t ∧
    LWidth (netPorts I) A (netInit I) B ω t ∧ WCorrect I A ω t ratio}

/-- `A` solves `α(n)`-Apx-MWC on undirected weighted CONGEST networks (weights in `[1, n^q]`, IDs
below `(max 2 n)^b`, messages below `(max 2 n)^B`) with high probability within `T(n)` rounds:
for some `c' > 0` and all large `n`, on every network of size `n` the success probability is at
least `1 - n^(-c')`. -/
def SolvesWeighted (A : LocalAlg) (α : ℕ → ℝ) (q b B : ℕ) (T : ℕ → ℕ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ I : Network n q b,
    ENNReal.ofReal (1 - (n : ℝ) ^ (-c')) ≤ tapeLaw n (WEvent I A B (α n) (T n))

/-! ### Directed unweighted inputs -/

/-- The underlying undirected graph of a digraph: the communication links. -/
def commGraph {V : Type} (D : Digraph V) : SimpleGraph V := SimpleGraph.fromRel D.Adj

/-- A directed CONGEST network: a loopless digraph (antiparallel arcs allowed) whose underlying
undirected graph is connected and carries bidirectional links, with unique IDs and private port
orders. -/
structure DNetwork (n b : ℕ) where
  D : Digraph (Fin n)
  loopless : ∀ v, ¬ D.Adj v v
  connected : (commGraph D).Connected
  id : Fin n → ℕ
  id_injective : Function.Injective id
  id_bound : ∀ v, id v < (max 2 n) ^ b
  ports : (v : Fin n) → Fin ((commGraph D).neighborSet v).ncard ≃ (commGraph D).neighborSet v

/-- Local direction code of the link `{v, u}` at `v`: bit 0 for the arc `v → u`, bit 1 for the
arc `u → v`. -/
def dirCode {V : Type} (D : Digraph V) (v u : V) : ℕ :=
  (if D.Adj v u then 1 else 0) + (if D.Adj u v then 2 else 0)

def dnetPorts {n b : ℕ} (I : DNetwork n b) : PortGraph n := ⟨commGraph I.D, I.ports⟩

/-- Initial knowledge: own ID and, per port, the neighbour's ID and the arc directions. -/
def dnetInit {n b : ℕ} (I : DNetwork n b) (v : Fin n) : ℕ × List ℕ :=
  (I.id v, List.ofFn fun p : Fin ((dnetPorts I).deg v) =>
    Nat.pair (I.id (I.ports v p).val) (dirCode I.D v (I.ports v p).val))

/-- Directed output convention: all nodes know the number of arcs of one common directed simple
cycle `C` with `w(C) ≤ ratio · OPT`; at both endpoints of every link, bit 0 of the mark says
whether the arc `v → u` belongs to `C` and bit 1 whether `u → v` does; on an acyclic input, the
common no-cycle output. -/
def DCorrect {n b : ℕ} (I : DNetwork n b) (A : LocalAlg) (ω : Tapes n) (t : ℕ)
    (ratio : ℝ) : Prop :=
  let s := lstate (dnetPorts I) A (dnetInit I) ω t
  (∃ C : DCycle I.D, (C.len : ℝ≥0∞) ≤ ENNReal.ofReal ratio * dOptimum I.D ∧
    ∀ v, A.value n (s v) = some C.len ∧
      ∀ p : Fin ((dnetPorts I).deg v),
        ((A.mark n (s v) p.val).testBit 0 = true ↔ C.HasArc v (I.ports v p).val) ∧
        ((A.mark n (s v) p.val).testBit 1 = true ↔ C.HasArc (I.ports v p).val v)) ∨
  (IsEmpty (DCycle I.D) ∧ ∀ v, A.value n (s v) = none ∧
    ∀ p < (dnetPorts I).deg v, A.mark n (s v) p = 0)

def DEvent {n b : ℕ} (I : DNetwork n b) (A : LocalAlg) (B : ℕ) (ratio : ℝ) (T : ℕ) :
    Set (Tapes n) :=
  {ω | ∃ t ≤ T, LHalted (dnetPorts I) A (dnetInit I) ω t ∧
    LWidth (dnetPorts I) A (dnetInit I) B ω t ∧ DCorrect I A ω t ratio}

/-- `A` solves `α(n)`-Apx-MWC on directed unweighted CONGEST networks with high probability
within `T(n)` rounds. -/
def SolvesDirected (A : LocalAlg) (α : ℕ → ℝ) (b B : ℕ) (T : ℕ → ℕ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ I : DNetwork n b,
    ENNReal.ofReal (1 - (n : ℝ) ^ (-c')) ≤ tapeLaw n (DEvent I A B (α n) (T n))

end DistributedMWC440.UpperBound.Supplement


