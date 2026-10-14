-- Prove2me | solution 1 for ActuarialValuation.pgAggregate_count_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:27:10.970216+00:00
-- url     : https://prove2.me/submissions/434af771-51ad-48eb-aa24-ebb58c2296d3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPointMass
import Definitions.Def_actuarial_pgAggregate
open ActuarialValuation

theorem solution(p f : ℕ → ℝ) (k : ℕ) : pgAggregate p f 0 k=p 0*pgPointMass k := by
  first
  | (simp [pgPointMass, pgAggregate, pgFold, pgConvolve]; done)
  | (norm_num [pgPointMass, pgAggregate, pgFold, pgConvolve]; done)
  | (unfold pgPointMass pgAggregate pgFold pgConvolve; positivity)
  | (simp only [pgPointMass, pgAggregate, pgFold, pgConvolve]; positivity)
  | (unfold pgPointMass pgAggregate pgFold pgConvolve; ring)
  | (unfold pgPointMass pgAggregate pgFold pgConvolve; simp; done)
  | (unfold pgPointMass pgAggregate pgFold pgConvolve; norm_num; done)
  | (simp [pgPointMass, pgAggregate, pgFold, pgConvolve]; ring)
  | (unfold pgPointMass pgAggregate pgFold pgConvolve; split_ifs <;> simp_all <;> linarith)
  | (unfold pgPointMass pgAggregate pgFold pgConvolve; nlinarith [sq_nonneg 0])
  | (simp_all [pgPointMass, pgAggregate, pgFold, pgConvolve]; done)
  | (unfold pgPointMass pgAggregate pgFold pgConvolve; simp_all; done)
  | rfl
