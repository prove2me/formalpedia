-- Prove2me | solution 1 for AdSCFT.anderson_thm_4_1
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T08:19:39.600964+00:00
-- url     : https://prove2.me/submissions/da32f4d5-6956-4f6e-be6a-efe2e7aa2e19

import Definitions.Def_AdSCFTFocusingProfiles
import Theorems.Thm_AdSCFT_initial_value_of_gauss
import Theorems.Thm_AdSCFT_focusing_bound

set_option autoImplicit false

open AdSCFT

-- AdSCFT.anderson_thm_4_1: Anderson's Theorem 4.1, estimate (4.2):
-- L² ≤ 4n(n-1)/Rγ when Rγ > 0.
-- Assembly of the two proved steps:
--   * AdSCFT.initial_value_of_gauss: (n-1)·φ(0) = Rγ/2 ⟹
--       φ(0) > 0 and 2n/φ(0) = 4n(n-1)/Rγ;
--   * AdSCFT.focusing_bound: FocusingProfileAH + φ(0) > 0 ⟹
--       L² ≤ 2n/φ(0).
-- Both deps are Proved on the platform, so this assembly is a full solve,
-- not a sketch.
theorem solution (n : ℕ) (hn : 2 ≤ n) (Rgamma L : ℝ) (hR : 0 < Rgamma)
    (hL : 0 ≤ L) (phi phi' : ℝ → ℝ) (hprofile : FocusingProfileAH n L phi phi')
    (hinit : ((n : ℝ) - 1) * phi 0 = Rgamma / 2) :
    L ^ 2 ≤ 4 * n * ((n : ℝ) - 1) / Rgamma := by
  have hn' : 0 < n := by omega
  obtain ⟨hpos, hval⟩ := AdSCFT.initial_value_of_gauss n hn Rgamma (phi 0) hR hinit
  have hfb := AdSCFT.focusing_bound n hn' L hL phi phi' hpos hprofile
  rw [hval] at hfb
  exact hfb
