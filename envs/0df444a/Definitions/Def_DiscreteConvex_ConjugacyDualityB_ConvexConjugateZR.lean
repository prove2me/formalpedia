-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateZR
-- name    : DiscreteConvex_ConjugacyDualityB_ConvexConjugateZR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:31:01.82456+00:00
-- url     : https://prove2.me/theorems/bd50a856-a60f-4a21-bd36-081e395f72fe
-- title:
--   ConvexConjugateZR
-- statement:
--   The Legendre-Fenchel transform of an integer-domain function, at a real point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.211-212, Eq. (8.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.211-212, Eq. (8.11)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ToEReal

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The Legendre-Fenchel transform of an integer-domain function, at a real point. -/
noncomputable def ConvexConjugateZR (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ x : V → ℤ, v = ((∑ i, p i * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x)}

end DiscreteConvex.ConjugacyDualityB


