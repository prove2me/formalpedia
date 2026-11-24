-- Prove2me | Definitions.Def_SourceProof_0fe51407ad89eab1ae3224f6
-- name    : SourceProof_0fe51407ad89eab1ae3224f6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:07:01.446261+00:00
-- url     : https://prove2.me/theorems/1206cfb3-970d-42e6-93f7-e3613d4217c4
-- title:
--   StochLean source theorem: StochLean.exists_second_deriv_remainder

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Order.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous quadratic Taylor quotient of a real C2 function

The diagonal is filled with one half of the second derivative, not the
totalized quotient's zero value. This is the coefficient of squared increments
in the exact finite-cell Taylor identity used for Ito's formula.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_0fe51407ad89eab1ae3224f6 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    ∃ c ∈ uIcc a b, f b - f a - deriv f a * (b - a) =
      (deriv (deriv f) c / 2) * (b - a) ^ 2 := by
  by_cases h : a = b
  · subst b
    exact ⟨a, left_mem_uIcc, by simp⟩
  · obtain ⟨c, hc, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) h hf.contDiffOn
    have hd : iteratedDerivWithin 1 f (uIcc a b) a = deriv f a := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc h)
        ((hf.of_le (by decide)).contDiffAt) left_mem_uIcc, iteratedDeriv_one]
    have ht : taylorWithinEval f 1 (uIcc a b) a b = f a + (b - a) * deriv f a := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval]
      norm_num [hd, smul_eq_mul]
    rw [ht] at he
    norm_num [iteratedDeriv_succ, iteratedDeriv_one] at he
    refine ⟨c, ⟨hc.1.le, hc.2.le⟩, ?_⟩
    nlinarith only [he]
end StochLean


