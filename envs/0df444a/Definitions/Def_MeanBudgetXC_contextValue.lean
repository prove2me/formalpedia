-- Prove2me | Definitions.Def_MeanBudgetXC_contextValue
-- name    : MeanBudgetXC_contextValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:33.378996+00:00
-- url     : https://prove2.me/theorems/6d3bec6e-5bf1-4401-9b28-298670c643e4
-- title:
--   The eliminated context value $F_S(q)$
-- statement:
--   For a set $S$ of $d$ vertices, the **eliminated context value** is
--   $$F_S(q)=\sum_{i\in S}T_i(q)-q(E(S)).$$
--   It is the value of the context objective at the minimum singleton lift $p=T(q)$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 3.2, p.11

import Mathlib
import Definitions.Def_MeanBudgetXC_topSum
import Definitions.Def_MeanBudgetXC_edgeMass

namespace MeanBudgetXC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **eliminated context value** `F_S(q) = ∑_{i ∈ S} T_i(q) − q(E(S))` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 3.2, p.11),
used for `|S| = d`. -/
def contextValue (d : ℕ) (q : Pair V → ℝ) (S : Finset V) : ℝ :=
  ∑ i ∈ S, topSum d q i - edgeMass q S

end MeanBudgetXC


