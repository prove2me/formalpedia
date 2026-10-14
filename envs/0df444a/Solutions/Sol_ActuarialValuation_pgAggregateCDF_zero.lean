-- Prove2me | solution 1 for ActuarialValuation.pgAggregateCDF_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:43:13.6866+00:00
-- url     : https://prove2.me/submissions/53bf7048-21b6-4d4a-8bab-326016ef5a0c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgAggregateCDF
open ActuarialValuation

theorem solution(p f : ℕ → ℝ) (m : ℕ) : pgAggregateCDF p f m 0=pgAggregate p f m 0 := by
  first
  | (simp [pgAggregate, pgFold, pgPointMass, pgConvolve, pgAggregateCDF]; done)
  | (norm_num [pgAggregate, pgFold, pgPointMass, pgConvolve, pgAggregateCDF]; done)
  | (unfold pgAggregate pgFold pgPointMass pgConvolve pgAggregateCDF; positivity)
  | (simp only [pgAggregate, pgFold, pgPointMass, pgConvolve, pgAggregateCDF]; positivity)
  | (unfold pgAggregate pgFold pgPointMass pgConvolve pgAggregateCDF; ring)
  | (unfold pgAggregate pgFold pgPointMass pgConvolve pgAggregateCDF; simp; done)
  | (unfold pgAggregate pgFold pgPointMass pgConvolve pgAggregateCDF; norm_num; done)
  | (simp [pgAggregate, pgFold, pgPointMass, pgConvolve, pgAggregateCDF]; ring)
  | (unfold pgAggregate pgFold pgPointMass pgConvolve pgAggregateCDF; split_ifs <;> simp_all <;> linarith)
  | (unfold pgAggregate pgFold pgPointMass pgConvolve pgAggregateCDF; nlinarith [sq_nonneg 0])
  | (simp_all [pgAggregate, pgFold, pgPointMass, pgConvolve, pgAggregateCDF]; done)
  | (unfold pgAggregate pgFold pgPointMass pgConvolve pgAggregateCDF; simp_all; done)
  | rfl
