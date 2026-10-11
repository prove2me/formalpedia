-- Prove2me | solution 1 for ActuarialValuation.clBFReserve_factor_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:39:21.826378+00:00
-- url     : https://prove2.me/submissions/31f1fd6b-08ca-46d1-bdd5-0779b61b3350

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clBFReserve
open ActuarialValuation

theorem solution(e : ℝ) : clBFReserve e 1 = 0 := by
  first
  | (simp [clBFReserve, clUnpaidFraction, clPaidFraction]; done)
  | (norm_num [clBFReserve, clUnpaidFraction, clPaidFraction]; done)
  | (unfold clBFReserve clUnpaidFraction clPaidFraction; positivity)
  | (simp only [clBFReserve, clUnpaidFraction, clPaidFraction]; positivity)
  | (unfold clBFReserve clUnpaidFraction clPaidFraction; ring)
  | (unfold clBFReserve clUnpaidFraction clPaidFraction; simp; done)
  | (unfold clBFReserve clUnpaidFraction clPaidFraction; norm_num; done)
  | (simp [clBFReserve, clUnpaidFraction, clPaidFraction]; ring)
  | (unfold clBFReserve clUnpaidFraction clPaidFraction; split_ifs <;> simp_all <;> linarith)
  | (unfold clBFReserve clUnpaidFraction clPaidFraction; nlinarith [sq_nonneg 0])
  | (simp_all [clBFReserve, clUnpaidFraction, clPaidFraction]; done)
  | (unfold clBFReserve clUnpaidFraction clPaidFraction; simp_all; done)
  | rfl
