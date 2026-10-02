-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_TRF
-- name    : DiscreteConvex_LConvexFunctions_TRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:36.98199+00:00
-- url     : https://prove2.me/theorems/f29c1100-b825-4254-b14b-a1389c4ab115
-- title:
--   Linearity along the all-ones direction (TRF[Z])
-- statement:
--   Axiom **(TRF[Z])**: $\exists r \in \mathbb R$ such that $g(p+\mathbf 1) = g(p) + r$ for all $p \in \mathbb Z^V$. A function $g$ with $\operatorname{dom} g \ne \emptyset$ satisfying (SBF[Z]) and (TRF[Z]) is an **L-convex function**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z])

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.177, axiom (TRF[Z]): linearity in the
direction of the all-ones vector, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- Axiom **(TRF[Z])**: `∃ r ∈ R` such that `g(p + 1) = g(p) + r` for all `p ∈ Zⱽ`, where `1`
is the all-ones vector. A function `g : Zⱽ → R ∪ {+∞}` with `dom g ≠ ∅` satisfying (SBF[Z]) and
(TRF[Z]) is an **L-convex function**. -/
def TRF {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.LConvexFunctions


