-- Prove2me | solution 1 for ActuarialValuation.clUnpaidFraction_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:05:41.341174+00:00
-- url     : https://prove2.me/submissions/9c3e2777-decd-41be-a192-0f0003ca70fb

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUnpaidFraction
open ActuarialValuation

theorem solution: clUnpaidFraction 1 = 0 := by
  first
  | (simp [clUnpaidFraction, clPaidFraction]; done)
  | (norm_num [clUnpaidFraction, clPaidFraction]; done)
  | (unfold clUnpaidFraction clPaidFraction; positivity)
  | (simp only [clUnpaidFraction, clPaidFraction]; positivity)
  | (unfold clUnpaidFraction clPaidFraction; ring)
  | (unfold clUnpaidFraction clPaidFraction; simp; done)
  | (unfold clUnpaidFraction clPaidFraction; norm_num; done)
  | (simp [clUnpaidFraction, clPaidFraction]; ring)
  | (unfold clUnpaidFraction clPaidFraction; split_ifs <;> simp_all <;> linarith)
  | (unfold clUnpaidFraction clPaidFraction; nlinarith [sq_nonneg 0])
  | (simp_all [clUnpaidFraction, clPaidFraction]; done)
  | (unfold clUnpaidFraction clPaidFraction; simp_all; done)
  | rfl
