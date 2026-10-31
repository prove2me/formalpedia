-- Prove2me | Definitions.Def_NieYangPareto_MOP_U
-- name    : NieYangPareto_MOP_U
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:26.459643+00:00
-- url     : https://prove2.me/theorems/51b08ca3-ab9a-41d3-ade9-a6c01b003e80
-- title:
--   The epigraph set $\mathcal U$ of (3.1)
-- statement:
--   For the problem (1.1), the **epigraph set** is
--
--   $$
--   \mathcal U:=\{u=(u_1,\dots,u_m)\mid u_i\ge f_i(x)\text{ for some }x\in K\},
--   $$
--
--   the same $x$ serving all coordinates $i$. Weakly Pareto values are read off the boundary of $\mathcal U$ (Proposition 3.1).
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, eq. (3.1), p.6

import Mathlib
import Definitions.Def_NieYangPareto_MOP

namespace NieYangPareto

variable {n m : ℕ} {E I : Type*}

/-- **The epigraph set (3.1).** Nie–Yang, arXiv:2108.04336v2, eq. (3.1), p.6:
`𝒰 = {u | u_i ≥ f_i(x) for some x ∈ K}`, the single `x` being shared by all `i`. -/
def MOP.U (P : MOP n m E I) : Set (Fin m → ℝ) :=
  {u | ∃ x ∈ P.K, ∀ i, P.obj x i ≤ u i}

end NieYangPareto


