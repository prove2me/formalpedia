-- Prove2me | Definitions.Def_KallMayer_Recourse_PointwiseRecourse
-- name    : KallMayer_Recourse_PointwiseRecourse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T03:59:27.119342+00:00
-- url     : https://prove2.me/theorems/2083f193-6a19-4366-8364-530c82647a86
-- title:
--   KallMayer_Recourse_PointwiseRecourse
-- statement:
--   Concrete book-local definitions from Definitions.Def_KallMayer_Recourse_PointwiseRecourse.
-- source:
--   kall-2005-stochastic-linear-programming

import Mathlib
import Definitions.Def_KallMayer_Recourse_LPValue

namespace KallMayer.Recourse

/-- Local provisional adapter for the pointwise recourse value in Kall–Mayer,
Chapter 3, (2.4)/(2.9), PDF209/213, and Theorem 2.2, PDF216 (printed207).
This composes the existing book-local LPValue with the residual h - T x;
it does not introduce a probability distribution or take an expectation.
The underlying LPValue and this wrapper are not claimed as published objects. -/
noncomputable def PointwiseRecourse {n₁ n₂ m : ℕ}
    (W : Matrix (Fin m) (Fin n₂) ℝ)
    (T : Matrix (Fin m) (Fin n₁) ℝ)
    (h : Fin m → ℝ) (q : Fin n₂ → ℝ) (x : Fin n₁ → ℝ) : EReal :=
  LPValue W q (h - Matrix.mulVec T x)

end KallMayer.Recourse


