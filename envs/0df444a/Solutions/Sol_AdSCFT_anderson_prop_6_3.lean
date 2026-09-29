-- Prove2me | solution 1 for AdSCFT.anderson_prop_6_3
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T10:35:18.911785+00:00
-- url     : https://prove2.me/submissions/f61d81dc-464e-4b1f-9264-ff1303a5ca59

import Definitions.Def_AdSCFTFocusingProfiles
import Theorems.Thm_AdSCFT_focusing_bound

set_option autoImplicit false

open AdSCFT

-- AdSCFT.anderson_prop_6_3: Proposition 6.3, estimate (6.16) — the de Sitter
-- counterpart of Theorem 4.1: L² ≤ 4n(n-1)/|Rγ| when Rγ < 0.
-- Reduction to the (Proved) AH focusing_bound via phi ↦ -phi:
--   FocusingProfileDS n L phi phi' unfolds to FocusingProfileAH n L (-phi) (-phi'),
-- since -(phi r)² = (phi r)² and negating flips the inequality to
--   -phi' r ≥ r·(-phi r)²/n.
-- The initial identity (n-1)·phi 0 = Rgamma/2 with Rgamma < 0 gives
--   -phi 0 = |Rgamma|/(2(n-1)),
-- so the AH bound L² ≤ 2n/(-phi 0) becomes L² ≤ 4n(n-1)/|Rgamma|.
theorem solution (n : ℕ) (hn : 2 ≤ n) (Rgamma L : ℝ) (hR : Rgamma < 0)
    (hL : 0 ≤ L) (phi phi' : ℝ → ℝ) (hprofile : FocusingProfileDS n L phi phi')
    (hinit : ((n : ℝ) - 1) * phi 0 = Rgamma / 2) :
    L ^ 2 ≤ 4 * n * ((n : ℝ) - 1) / |Rgamma| := by
  obtain ⟨hder, hineq⟩ := hprofile
  have hn' : 0 < n := by omega
  have hnm1 : (0:ℝ) < (n:ℝ) - 1 := by
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- Step 1: phi 0 < 0 from (n-1)·phi 0 = Rgamma/2 < 0.
  have hphi0 : phi 0 < 0 := by
    have h2 : ((n:ℝ) - 1) * phi 0 < 0 := by rw [hinit]; linarith
    by_contra h
    have hnn : (0:ℝ) ≤ phi 0 := not_lt.mp h
    have h3 : (0:ℝ) ≤ ((n:ℝ) - 1) * phi 0 :=
      mul_nonneg (le_of_lt hnm1) hnn
    linarith
  have hneg : (0:ℝ) < -phi 0 := neg_pos.mpr hphi0
  -- Step 2: the negated profile satisfies the AH focusing profile.
  have hAH : FocusingProfileAH n L (fun r => -phi r) (fun r => -(phi' r)) := by
    refine ⟨?_, ?_⟩
    · intro r hr
      exact (hder r hr).neg
    · intro r hr
      show r * (-phi r) ^ 2 / (n:ℝ) ≤ -(phi' r)
      rw [neg_sq]
      have h := hineq r hr
      linarith
  -- Step 3: apply the proved AH focusing bound to the negated profile.
  have hfb : L ^ 2 ≤ 2 * (n:ℝ) / (-phi 0) :=
    AdSCFT.focusing_bound n hn' L hL (fun r => -phi r) (fun r => -(phi' r)) hneg hAH
  -- Step 4: 2n/(-phi 0) = 4n(n-1)/|Rgamma|.
  have habs : |Rgamma| = -Rgamma := abs_of_neg hR
  have hval : 2 * (n:ℝ) / (-phi 0) = 4 * n * ((n:ℝ) - 1) / |Rgamma| := by
    have hne2 : -phi 0 ≠ 0 := neg_ne_zero.mpr (ne_of_lt hphi0)
    have hne3 : |Rgamma| ≠ 0 := by
      rw [habs]; exact neg_ne_zero.mpr (ne_of_lt hR)
    rw [div_eq_div_iff hne2 hne3, habs]
    linear_combination 4 * (n:ℝ) * hinit
  rw [hval] at hfb
  exact hfb
