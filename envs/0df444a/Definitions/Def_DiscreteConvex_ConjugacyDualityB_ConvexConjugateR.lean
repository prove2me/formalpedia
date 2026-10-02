-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateR
-- name    : DiscreteConvex_ConjugacyDualityB_ConvexConjugateR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:30:57.868726+00:00
-- url     : https://prove2.me/theorems/74c4203d-3d6b-4f72-b09e-1c616f98c2d2
-- title:
--   ConvexConjugateR
-- statement:
--   The real Legendre-Fenchel transform of a real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.3).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.3)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ToEReal

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The real Legendre-Fenchel transform of a real-domain function. -/
noncomputable def ConvexConjugateR (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ x : V → ℝ, v = ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f x)}

end DiscreteConvex.ConjugacyDualityB


