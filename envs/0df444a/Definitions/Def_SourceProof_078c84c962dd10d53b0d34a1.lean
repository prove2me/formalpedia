-- Prove2me | Definitions.Def_SourceProof_078c84c962dd10d53b0d34a1
-- name    : SourceProof_078c84c962dd10d53b0d34a1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:37.785917+00:00
-- url     : https://prove2.me/theorems/8281beff-ad1e-4c19-8970-15b4a544de90
-- title:
--   StochLean source theorem: ProbabilityTheory.integral_natCast_poisson

import Definitions.Def_StochLean_Probability_Process_Poisson_IntervalAxioms_F000
import Definitions.Def_SourceProof_db86699b96bdd02e6e9ffb79
import Mathlib.Analysis.SpecialFunctions.Exponential

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # First moments of the actual Poisson counting process

The Poisson series gives the exact first moment, including rate zero.
The existing law and integrability interfaces transfer it to process values
and real increments. No martingale or bracket condition is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_078c84c962dd10d53b0d34a1 (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  have hs := hasSum_integral_poissonMeasure (_root_.Prove2MeSourceProof.h_db86699b96bdd02e6e9ffb79 r)
  rw [integral_poissonMeasure', hs.summable.tsum_eq_zero_add]
  · simp only [smul_eq_mul, Nat.cast_zero, mul_zero, zero_add]
    have he (n : ℕ) : Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) /
        ((n + 1).factorial : ℝ) * (n + 1 : ℕ) =
        (Real.exp (-(r : ℝ)) * (r : ℝ)) * ((r : ℝ) ^ n / (n.factorial : ℝ)) := by
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    simp_rw [he]
    rw [tsum_mul_left]
    have hexp : (∑' n : ℕ, (r : ℝ) ^ n / (n.factorial : ℝ)) = Real.exp r := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hexp, mul_right_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  · exact _root_.Prove2MeSourceProof.h_db86699b96bdd02e6e9ffb79 r
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

end ProbabilityTheory


