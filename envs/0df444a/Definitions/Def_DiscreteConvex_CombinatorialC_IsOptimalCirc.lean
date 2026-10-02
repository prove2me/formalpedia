-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_IsOptimalCirc
-- name    : DiscreteConvex_CombinatorialC_IsOptimalCirc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:44:08.296133+00:00
-- url     : https://prove2.me/theorems/fdf6b683-7298-483e-87df-a38c5adcf4d2
-- title:
--   Optimal circulation for a weight vector
-- statement:
--   $\xi$ is feasible and maximizes $\langle w,\cdot\rangle$ among feasible circulations for $c$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.87.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.87

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsFeasibleCirc

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.87 ("ξ1 is optimal for w1"): an optimal
circulation, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `ξ` is **optimal** for weight `w` (with capacity `c`): `ξ` is feasible and maximizes
`⟨w, ·⟩` among all feasible circulations for `c`. -/
def IsOptimalCirc {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c : A → ℝ) (xi : A → ℝ) : Prop :=
  IsFeasibleCirc src dst c xi ∧
    ∀ xi', IsFeasibleCirc src dst c xi' → dotProduct w xi' ≤ dotProduct w xi

end DiscreteConvex.CombinatorialC


