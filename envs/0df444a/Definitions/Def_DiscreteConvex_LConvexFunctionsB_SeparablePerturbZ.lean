-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_SeparablePerturbZ
-- name    : DiscreteConvex_LConvexFunctionsB_SeparablePerturbZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:21:06.788103+00:00
-- url     : https://prove2.me/theorems/359e177d-e167-4659-b87d-30a3f7585cc7
-- title:
--   SeparablePerturbZ
-- statement:
--   The infimal convolution of $g$ with a separable convex function, Eq. (7.18).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.183, Eq. (7.18).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.183, Eq. (7.18)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The infimal convolution of `g` with a separable convex function, Eq. (7.18). -/
noncomputable def SeparablePerturbZ (g : (V → ℤ) → WithTop ℝ) (psi : V → ℤ → WithTop ℝ)
    (p : V → ℤ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ q : V → ℤ, L = g q + ∑ v, psi v (p v - q v)}

end DiscreteConvex.LConvexFunctionsB


