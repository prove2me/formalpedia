-- Prove2me | Definitions.Def_SourceProof_bca5f30d001e49e5350a130a
-- name    : SourceProof_bca5f30d001e49e5350a130a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:01:16.291817+00:00
-- url     : https://prove2.me/theorems/dba06be9-9ef0-4d94-a7a5-29656f090e40
-- title:
--   StochLean source theorem: ProbabilityTheory.integral_natCast_sq_poisson

import Definitions.Def_SourceProof_078c84c962dd10d53b0d34a1
import Definitions.Def_SourceProof_b5b4d599cb73f64707c76f41
import Definitions.Def_SourceProof_db86699b96bdd02e6e9ffb79

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Second moments of Poisson counts

The series shift proves square integrability and the exact second moment.
Ordered real increments inherit both results from their existing Poisson law.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_bca5f30d001e49e5350a130a (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) ^ 2 + r := by
  have hs := hasSum_integral_poissonMeasure (_root_.Prove2MeSourceProof.h_b5b4d599cb73f64707c76f41 r)
  rw [integral_poissonMeasure' (_root_.Prove2MeSourceProof.h_b5b4d599cb73f64707c76f41 r),
    hs.summable.tsum_eq_zero_add]
  simp only [smul_eq_mul, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_add]
  have he (n : ℕ) : Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) /
      ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n /
        (n.factorial : ℝ) * ((n : ℝ) + 1)) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  simp_rw [he]
  rw [tsum_mul_left]
  have hi := integral_poissonMeasure'
    ((_root_.Prove2MeSourceProof.h_db86699b96bdd02e6e9ffb79 r).add (integrable_const (1 : ℝ)))
  simp only [Pi.add_apply, smul_eq_mul] at hi
  rw [← hi, integral_add (_root_.Prove2MeSourceProof.h_db86699b96bdd02e6e9ffb79 r) (integrable_const (1 : ℝ)),
    _root_.Prove2MeSourceProof.h_078c84c962dd10d53b0d34a1]
  simp only [integral_const, probReal_univ, one_smul]
  ring
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

end ProbabilityTheory


