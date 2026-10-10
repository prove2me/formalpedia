-- Prove2me | solution 1 for ActuarialValuation.annualDecrementLaw_survival_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:50:13.10881+00:00
-- url     : https://prove2.me/submissions/3d0f01ba-c2ab-483c-893f-0155680f16b3

import Mathlib
import Definitions.Def_actuarial_isAnnualDecrementLaw
open MeasureTheory
open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (p : ℝ) (q : J → ℝ)
  (h : isAnnualDecrementLaw p q)
  :
  0 ≤ p := h.1
