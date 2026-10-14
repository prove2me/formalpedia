-- Prove2me | solution 2 for ActuarialValuation.jlReversionaryPayment_zero_spouse
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:40.576857+00:00
-- url     : https://prove2.me/submissions/80f0ecd7-2636-4013-bee5-c38b48e80022

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlReversionaryPayment

open ActuarialValuation

theorem solution (px benefit : ℝ) : jlReversionaryPayment px 0 benefit=0 := by simp [jlReversionaryPayment]

