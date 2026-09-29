-- Prove2me | Definitions.Def_KallMayer_Recourse_CompleteRecourse
-- name    : KallMayer_Recourse_CompleteRecourse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T03:58:32.671173+00:00
-- url     : https://prove2.me/theorems/07c04683-f4dd-422a-a045-aa7024668086
-- title:
--   KallMayer_Recourse_CompleteRecourse
-- statement:
--   Concrete book-local definitions from Definitions.Def_KallMayer_Recourse_CompleteRecourse.
-- source:
--   kall-2005-stochastic-linear-programming

import Mathlib

namespace KallMayer.Recourse

/-- Complete fixed recourse: every right-hand side has a nonnegative recourse
vector. Kall–Mayer (2005), Chapter 3, equation (2.6), printed p. 201. -/
def CompleteRecourse {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ z : Fin m → ℝ, ∃ y : Fin n → ℝ,
    (∀ j, 0 ≤ y j) ∧ Matrix.mulVec W y = z

end KallMayer.Recourse


