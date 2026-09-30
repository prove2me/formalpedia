-- Prove2me | Definitions.Def_PadbergRao_OddCut_IsMinOddPairCut
-- name    : PadbergRao_OddCut_IsMinOddPairCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:45:48.520315+00:00
-- url     : https://prove2.me/theorems/ba01a8e2-64f1-435a-9055-0d16af1149cd
-- title:
--   Minimum cut-set with respect to all pairs of odd labelled nodes
-- statement:
--   Let $V_1 \subseteq V$ be the set of odd-labelled nodes. A cut-set $(U : V - U)$ **separates a pair of odd nodes** if there are odd nodes $p \in U$ and $q \in V - U$.
--
--   A cut-set $(M : V - M)$ is a **minimum cut-set with respect to all pairs of odd labelled nodes** if it separates some pair of odd nodes and
--
--   $$
--   c(M : V - M) \;\le\; c(U : V - U) \quad \text{for every } U \subseteq V \text{ separating a pair of odd nodes.}
--   $$
--
--   Equivalently, its capacity is the smallest capacity of a minimum $p$–$q$ cut over all pairs $p, q$ of odd nodes. This is the cut-set that Lemma 1.1 relates to odd minimum cut-sets.
--
--   **Formalization Note** `SeparatesOddPair odd U := ∃ p ∈ odd, ∃ q ∈ odd, p ∈ U ∧ q ∉ U`; minimality is a lower bound against every separating $U$.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 68, Lemma 1.1

import Mathlib
import Definitions.Def_PadbergRao_OddCut_cutCapacity

namespace PadbergRao.OddCut

/-- The cut-set `(U : V − U)` separates some pair of odd-labelled nodes: there are odd nodes
`p ∈ U` and `q ∉ U`. Padberg–Rao 1982, p. 68, Lemma 1.1. -/
def SeparatesOddPair {V : Type*} (odd U : Finset V) : Prop :=
  ∃ p ∈ odd, ∃ q ∈ odd, p ∈ U ∧ q ∉ U

/-- `(M : V − M)` is a minimum cut-set with respect to all pairs of odd labelled nodes:
it separates two odd nodes, and its capacity is at most that of every cut-set separating two
odd nodes. Padberg–Rao 1982, p. 68, Lemma 1.1. -/
def IsMinOddPairCut {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (odd M : Finset V) :
    Prop :=
  SeparatesOddPair odd M ∧
    ∀ U : Finset V, SeparatesOddPair odd U → cutCapacity c M ≤ cutCapacity c U

end PadbergRao.OddCut


