-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossTail_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:50:17.204176+00:00
-- url     : https://prove2.me/submissions/655ff1ec-8314-4f48-8885-9e75f29d3449

import Mathlib
import Definitions.Def_actuarial_discreteStopLossTail
open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ discreteStopLossTail w bound deductible := by
  unfold discreteStopLossTail
  refine Finset.sum_nonneg fun s _ => ?_
  split_ifs
  · exact hw s
  · exact le_rfl
