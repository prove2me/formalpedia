-- Prove2me | solution 1 for ActuarialValuation.coFGM_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:49:49.800907+00:00
-- url     : https://prove2.me/submissions/bcd185b4-3103-4d22-a779-3e8ac25e2786

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coFGM
open ActuarialValuation

theorem solution(theta u v : ℝ) : coFGM theta u v=coFGM theta v u := by
  unfold coFGM
  ring
