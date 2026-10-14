-- Prove2me | solution 2 for ActuarialValuation.crRatingExpectedPay_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:40.510991+00:00
-- url     : https://prove2.me/submissions/9510cb5e-a47a-43ad-b421-96b56ce4111e

import Mathlib
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_crRatingExpectedPay

open ActuarialValuation

theorem solution (P : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : crRatingExpectedPay P i (fun _ => 0)=0 := by simp [crRatingExpectedPay]

