-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_FlowCompilation
-- name    : ChenCapacityTerminals_Exact_FlowCompilation
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T05:37:58.676542+00:00
-- url     : https://prove2.me/theorems/79a40e78-21db-46d3-aa14-54bd31351cf5
-- title:
--   Scalar fixed-pair flow executions and almost-linear runtime
-- statement:
--   This module specifies an ordinary bounded-word implementation of the fixed-pair primitive used by the headline algorithm.
--
--   For a query $Q$ on $n_Q$ vertices with raw integral arc records, the scalar program must return an integral arc-flow list and a $0/1$ vertex shore satisfying the existing exact `FlowCutAnswer` correctness predicate. Both output components are charged. A run is an actual execution of a finite `TrulySubcubicAPSP` program, not an uninterpreted function assigned a cost.
--
--   The numerical-class predicate uses a common scale $N$: the query has size at most $N^p$ and capacities at most $N^q$. This allows a small submitted network to inherit capacity bounds from the original input. A **fast** solver works uniformly for every such class and, for every $\varepsilon>0$, has a uniform bound
--   $$
--   C\,(n_Q+|E_Q|+2)^{1+\varepsilon}
--     \bigl(\log(2+2N)\bigr)^k.
--   $$
--   The local network size carries the almost-linear exponent, while the common scale appears only polylogarithmically. This is the bounded-word form needed for summing the fixed-pair costs in Theorem 1.1.
--
--   **Formalization Note** The definitions use the same arc-record, flow-and-shore, and scalar-execution semantics as the mission’s headline predicates; no oracle or mathematical-function instruction is added.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, proof of Theorem 1.1, paper p.9 (PDF p.10), final paragraph; van den Brand et al., FOCS 2023, Theorem 1.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10 ; https://arxiv.org/pdf/2309.16629#page=4

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

/-- Input words for one integral fixed-pair maximum-flow computation. -/
def queryWords (Q : IntegerQuery) : List ℤ :=
  [(Q.graph.n : ℤ), (Q.graph.arcs.length : ℤ),
    (Q.source : ℤ), (Q.sink : ℤ)] ++ arcWords Q.graph.arcs

/-- The charged output region contains a flow value for every raw arc and a
0/1 indicator for every vertex. -/
def FlowWordOutput {W : ℕ} (Q : IntegerQuery) (m : ℤ → BitVec W) : Prop :=
  let base := (queryWords Q).length
  ∃ A : IntegerAnswer, A.Correct Q ∧
    A.flow = (List.range Q.graph.arcs.length).map (fun i =>
      (m (base + i : ℕ)).toNat) ∧
    A.shore = (Finset.range Q.graph.n).filter (fun v =>
      (m (base + Q.graph.arcs.length + v : ℕ)).toNat = 1)

/-- Ordinary scalar execution of an integral fixed-pair solver. -/
def PlainFlowRun (S : List TrulySubcubicAPSP.Instr) (W time : ℕ)
    (Q : IntegerQuery) : Prop :=
  ∃ ticks m, TrulySubcubicAPSP.exec S ticks 0
    (TrulySubcubicAPSP.loadWords W (queryWords Q)) = some (true, m) ∧
    FlowWordOutput Q m ∧
    time = ticks + (queryWords Q).length + Q.graph.n + Q.graph.arcs.length

/-- Polynomial size/capacity bounds relative to a common numerical scale.
The scale can be the original input size even when a submitted query is small. -/
def FlowNumericClass (Q : IntegerQuery) (scale p q : ℕ) : Prop :=
  Q.Valid ∧ 2 ≤ scale ∧ Q.graph.n + Q.graph.arcs.length ≤ scale ^ p ∧
    ∀ e ∈ Q.graph.arcs, e.capacity ≤ scale ^ q

/-- A deterministic almost-linear fixed-pair implementation. Its time depends
only polylogarithmically on the common numerical scale; the almost-linear power
is in the local network size. -/
def FastWordFlow (S : List TrulySubcubicAPSP.Instr) : Prop :=
  ∀ p q : ℕ, ∃ B : ℕ, ∃ k : ℕ, 0 < B ∧
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (Q : IntegerQuery) (scale : ℕ), FlowNumericClass Q scale p q →
        ∀ W ≥ B * (Nat.log2 scale + 1), ∃ time : ℕ,
          (time : ℝ) ≤ C * (Q.graph.n + Q.graph.arcs.length + 2 : ℕ) ^ (1 + ε) *
            polylog scale scale k ∧
          PlainFlowRun S W time Q

end ChenCapacityTerminals.Exact


