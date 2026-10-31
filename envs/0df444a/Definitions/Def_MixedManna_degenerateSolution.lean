-- Prove2me | Definitions.Def_MixedManna_degenerateSolution
-- name    : MixedManna_degenerateSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:28.926719+00:00
-- url     : https://prove2.me/theorems/be5a0eb7-d3e5-45d5-910d-9f03855f3b35
-- title:
--   The degenerate solution $p=P$, $r=R$
-- statement:
--   The **degenerate solution** sets $p_j=P$ for all $j\in M$, $r_i=R$ for all $i\in N$, and all other variables, $z$ included, to zero. It solves LCP (14), but all relative prices are zero and nothing is allocated, so it is not a competitive equilibrium.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §4.2.1 p.20 and Lemma 19, p.26

import Mathlib
import Definitions.Def_MixedManna_LCPVar

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

/-- **The degenerate solution** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a
Mixed Manna*, arXiv:2008.02753v1, p.20 and Lemma 19, p.26): `p_j = P` for all `j ∈ M`,
`r_i = R` for all `i ∈ N`, and all other variables, including `z`, equal to zero. It solves LCP
(14) but is not a competitive equilibrium (all relative prices are zero). -/
def degenerateSolution (I : Instance N M) (P R : ℝ) : LCPVar I :=
  (fun _ => P, 0, fun _ => R, 0, 0)

end MixedManna


