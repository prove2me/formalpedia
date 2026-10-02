-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConcaveConjugateZR
-- name    : DiscreteConvex_ConjugacyDualityB_ConcaveConjugateZR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:31:30.818957+00:00
-- url     : https://prove2.me/theorems/25be719c-2413-469b-933e-2216feb5ba06
-- title:
--   ConcaveConjugateZR
-- statement:
--   The concave conjugate $h^\circ(p) = \inf_x[\langle p,x\rangle - h(x)]$, computed from $h_2=-h$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.217, Eq. (8.12)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.217, Eq. (8.12)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ToEReal

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The concave conjugate `h◦(p) = inf_x [⟨p,x⟩ - h(x)]`, computed from `h2 = -h`. -/
noncomputable def ConcaveConjugateZR (h2 : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : EReal :=
  sInf {v : EReal | ∃ x : V → ℤ, v = ((∑ i, p i * (x i : ℝ) : ℝ) : EReal) + ToEReal (h2 x)}

end DiscreteConvex.ConjugacyDualityB


