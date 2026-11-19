-- Prove2me | solution 1 for AlmostKing.Query.observation_10
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:36:51.645103+00:00
-- url     : https://prove2.me/submissions/fbe069ac-e00d-4a51-8706-4a04694dfa08

import Definitions.Def_AlmostKing_Query_Regularity

theorem solution (τ η : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 2) (hη : 0 ≤ η) :
    1 - 2 * τ - 2 * η ≤ (1 - 2 * τ) * (1 - η)^2 := by
  nlinarith [mul_nonneg hτ hη, mul_nonneg (sub_nonneg.2 (by linarith : 2 * τ ≤ 1)) (sq_nonneg η)]
