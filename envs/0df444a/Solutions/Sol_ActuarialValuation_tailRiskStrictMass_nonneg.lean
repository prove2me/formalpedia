-- Prove2me | solution 1 for ActuarialValuation.tailRiskStrictMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:41:25.388427+00:00
-- url     : https://prove2.me/submissions/72b3439e-9d60-4e7f-bd7b-70fa4a81ad3d

import Mathlib
import Definitions.Def_actuarial_tailRiskStrictMass
open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound q : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ tailRiskStrictMass w bound q := by
  unfold tailRiskStrictMass
  refine Finset.sum_nonneg fun s _ => ?_
  split_ifs
  · exact hw s
  · exact le_rfl

