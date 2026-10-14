-- Prove2me | solution 2 for ActuarialValuation.jlReversionaryPayment_zero_no_death
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:40.799523+00:00
-- url     : https://prove2.me/submissions/1fe2e97f-b61e-4f50-8328-c51969b50d4a

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlReversionaryPayment

open ActuarialValuation

theorem solution (py benefit : ℝ) : jlReversionaryPayment 1 py benefit=0 := by simp [jlReversionaryPayment]

