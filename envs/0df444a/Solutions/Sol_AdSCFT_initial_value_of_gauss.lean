-- Prove2me | solution 1 for AdSCFT.initial_value_of_gauss
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T07:31:29.221578+00:00
-- url     : https://prove2.me/submissions/ee956d08-073f-465b-9144-e7555c9810cf

import Definitions.Def_AdSCFTFocusingProfiles

set_option autoImplicit false

-- AdSCFT.initial_value_of_gauss: initial value (4.8).
-- From (n-1) * c = Rgamma / 2 with 2 ≤ n and 0 < Rgamma:
--   (i) 0 < c  (since (n:ℝ)-1 > 0 and the product is positive),
--   (ii) 2*n/c = 4*n*(n-1)/Rgamma  (clear denominators via div_eq_div_iff,
--        substitute Rgamma = 2*(n-1)*c, close by ring).
theorem solution (n : ℕ) (hn : 2 ≤ n) (Rgamma c : ℝ) (hR : 0 < Rgamma)
    (hc : ((n : ℝ) - 1) * c = Rgamma / 2) :
    0 < c ∧ 2 * n / c = 4 * n * ((n : ℝ) - 1) / Rgamma := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hpos : 0 < ((n : ℝ) - 1) * c := by rw [hc]; linarith
  have hc0 : 0 < c := pos_of_mul_pos_right hpos (le_of_lt hnm1)
  refine ⟨hc0, ?_⟩
  have hR2 : Rgamma = 2 * ((n : ℝ) - 1) * c := by linarith
  rw [div_eq_div_iff (ne_of_gt hc0) (ne_of_gt hR), hR2]
  ring
