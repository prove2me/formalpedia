-- Prove2me | solution 1 for ActuarialValuation.ipTail_balance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:22:56.023982+00:00
-- url     : https://prove2.me/submissions/2541bbbb-fd7e-4b80-9e59-7c82a51f94fe

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipCDF
import Definitions.Def_actuarial_ipTail
open ActuarialValuation

theorem solution(p f : ℕ → ℝ) (k : ℕ) : ipTail p f k+ipCDF p f k=1 := by
  first
  | (simp [ipCDF, ipCompound, ipFold, ipPoint, ipConvolve, ipTail]; done)
  | (norm_num [ipCDF, ipCompound, ipFold, ipPoint, ipConvolve, ipTail]; done)
  | (unfold ipCDF ipCompound ipFold ipPoint ipConvolve ipTail; positivity)
  | (simp only [ipCDF, ipCompound, ipFold, ipPoint, ipConvolve, ipTail]; positivity)
  | (unfold ipCDF ipCompound ipFold ipPoint ipConvolve ipTail; ring)
  | (unfold ipCDF ipCompound ipFold ipPoint ipConvolve ipTail; simp; done)
  | (unfold ipCDF ipCompound ipFold ipPoint ipConvolve ipTail; norm_num; done)
  | (simp [ipCDF, ipCompound, ipFold, ipPoint, ipConvolve, ipTail]; ring)
  | (unfold ipCDF ipCompound ipFold ipPoint ipConvolve ipTail; split_ifs <;> simp_all <;> linarith)
  | (unfold ipCDF ipCompound ipFold ipPoint ipConvolve ipTail; nlinarith [sq_nonneg 0])
  | (simp_all [ipCDF, ipCompound, ipFold, ipPoint, ipConvolve, ipTail]; done)
  | (unfold ipCDF ipCompound ipFold ipPoint ipConvolve ipTail; simp_all; done)
  | rfl
