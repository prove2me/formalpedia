-- Prove2me | solution 1 for AdSCFT.trace_sq_le_card_mul_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T07:18:35.544983+00:00
-- url     : https://prove2.me/submissions/f9e15771-c297-49a9-a5d1-c093a8a13b5e

import Definitions.Def_AdSCFTFocusingProfiles

set_option autoImplicit false

-- AdSCFT.trace_sq_le_card_mul_sum_sq: trace Cauchy-Schwarz,
-- (∑ᵢ vᵢ)² ≤ n · ∑ᵢ vᵢ² for v : Fin n → ℝ.
-- Direct application of Mathlib's sq_sum_le_card_mul_sum_sq
-- (Chebyshev/Cauchy-Schwarz special case).
theorem solution (n : ℕ) (v : Fin n → ℝ) :
    (∑ i, v i) ^ 2 ≤ n * ∑ i, (v i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := v)
  simpa using h
