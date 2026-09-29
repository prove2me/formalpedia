-- Prove2me | Definitions.Def_KallMayer_Recourse_ExpectedRecourse
-- name    : KallMayer_Recourse_ExpectedRecourse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T04:00:21.700519+00:00
-- url     : https://prove2.me/theorems/3fe596b6-a765-4959-b741-1f498d8d7b26
-- title:
--   KallMayer_Recourse_ExpectedRecourse
-- statement:
--   Concrete book-local definitions from Definitions.Def_KallMayer_Recourse_ExpectedRecourse.
-- source:
--   kall-2005-stochastic-linear-programming

import Mathlib
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse

open MeasureTheory

namespace KallMayer.Recourse

/-- Local provisional adapter for the expected recourse in Chapter 3 (2.3),
PDF209, and Theorem 2.3, PDF217–218 (printed208–209).
This is the real Bochner integral of the real projection of the existing
extended-real pointwise value. Outside the finite-a.e., integrable regime it
is only a totalized adapter, not an extended-real expectation: `toReal` sends
infinities to zero and the Bochner integral is zero for nonintegrable inputs.
The capstone explicitly concludes finiteness and integrability, so neither
convention can conceal a divergent recourse cost in its application.
No finite-support assumption is made; this is not a published platform object. -/
noncomputable def ExpectedRecourse {Ω : Type*} [MeasurableSpace Ω]
    {n₁ n₂ m : ℕ} (μ : Measure Ω)
    (W : Matrix (Fin m) (Fin n₂) ℝ)
    (T : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (h : Ω → Fin m → ℝ) (q : Ω → Fin n₂ → ℝ)
    (x : Fin n₁ → ℝ) : ℝ :=
  ∫ ξ, (PointwiseRecourse W (T ξ) (h ξ) (q ξ) x).toReal ∂μ

end KallMayer.Recourse


