-- Prove2me | solution 1 for ActuarialValuation.ipCDF_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:53:49.719143+00:00
-- url     : https://prove2.me/submissions/f1927126-e0ff-476f-819c-bdbdd1d92095

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipCompound
import Definitions.Def_actuarial_ipCDF
open ActuarialValuation

theorem solution(p f : ℕ → ℝ) : ipCDF p f 0=ipCompound p f 0 := by
  first
  | (simp [ipCompound, ipFold, ipPoint, ipConvolve, ipCDF]; done)
  | (norm_num [ipCompound, ipFold, ipPoint, ipConvolve, ipCDF]; done)
  | (unfold ipCompound ipFold ipPoint ipConvolve ipCDF; positivity)
  | (simp only [ipCompound, ipFold, ipPoint, ipConvolve, ipCDF]; positivity)
  | (unfold ipCompound ipFold ipPoint ipConvolve ipCDF; ring)
  | (unfold ipCompound ipFold ipPoint ipConvolve ipCDF; simp; done)
  | (unfold ipCompound ipFold ipPoint ipConvolve ipCDF; norm_num; done)
  | (simp [ipCompound, ipFold, ipPoint, ipConvolve, ipCDF]; ring)
  | (unfold ipCompound ipFold ipPoint ipConvolve ipCDF; split_ifs <;> simp_all <;> linarith)
  | (unfold ipCompound ipFold ipPoint ipConvolve ipCDF; nlinarith [sq_nonneg 0])
  | (simp_all [ipCompound, ipFold, ipPoint, ipConvolve, ipCDF]; done)
  | (unfold ipCompound ipFold ipPoint ipConvolve ipCDF; simp_all; done)
  | rfl
