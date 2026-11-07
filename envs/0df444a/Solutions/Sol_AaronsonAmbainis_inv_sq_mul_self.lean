-- Prove2me | solution 1 for AaronsonAmbainis.inv_sq_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:18:32.028909+00:00
-- url     : https://prove2.me/submissions/e6937c72-ad1f-4eda-bea4-629f78a518e3

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution (s : ℝ) : s⁻¹ ^ 2 * s = s⁻¹ := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [pow_two, mul_assoc, inv_mul_cancel₀ hs, mul_one]
end AaronsonAmbainis
