-- Prove2me | solution 1 for ActuarialValuation.tailRiskTVaR_ge_quantile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:58:45.315007+00:00
-- url     : https://prove2.me/submissions/b7a7b517-1b3c-45ed-82e9-18bcc3163195

import Mathlib
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskStopLoss
import Theorems.Thm_ActuarialValuation_tailRiskTVaR_stoploss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (hw : ∀ s, 0 ≤ w s) (ha : alpha < 1) :
  (q : ℝ) ≤ tailRiskTVaR w bound q alpha := by
  have hstop : 0 ≤ tailRiskStopLoss w bound q := by
    unfold tailRiskStopLoss
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (Nat.cast_nonneg _) (hw s)
  have hden : 0 ≤ 1 - alpha := by linarith
  rw [ActuarialValuation.tailRiskTVaR_stoploss w bound q alpha ha]
  have hratio := div_nonneg hstop hden
  linarith
