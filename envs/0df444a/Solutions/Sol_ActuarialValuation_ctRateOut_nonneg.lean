-- Prove2me | solution 1 for ActuarialValuation.ctRateOut_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:05:03.991498+00:00
-- url     : https://prove2.me/submissions/2bff0dcf-fe4e-4439-bb69-ad94234f6bba

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRateOut
open ActuarialValuation

theorem solution(r : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (hr : ∀ j, 0 ≤ r i j) : 0 ≤ ctRateOut r i := by
  unfold ctRateOut
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact hr j
