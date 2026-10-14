-- Prove2me | solution 2 for ActuarialValuation.jlPostPremiumFund_zero_interest
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:42.874738+00:00
-- url     : https://prove2.me/submissions/2fd409b2-c5a6-482d-a101-6606dc90926a

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlPostPremiumFund

open ActuarialValuation

theorem solution (reserve premium : ℝ) : jlPostPremiumFund reserve premium 0=reserve+premium := by simp [jlPostPremiumFund]

