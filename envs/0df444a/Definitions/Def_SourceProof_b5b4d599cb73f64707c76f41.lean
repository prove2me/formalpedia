-- Prove2me | Definitions.Def_SourceProof_b5b4d599cb73f64707c76f41
-- name    : SourceProof_b5b4d599cb73f64707c76f41
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:36.238135+00:00
-- url     : https://prove2.me/theorems/931243ed-0ce9-41ae-9648-de3607135f02
-- title:
--   StochLean source theorem: ProbabilityTheory.integrable_natCast_sq_poisson

import Definitions.Def_SourceProof_db86699b96bdd02e6e9ffb79
import Mathlib.Analysis.SpecialFunctions.Exponential

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

theorem _root_.Prove2MeSourceProof.h_b5b4d599cb73f64707c76f41 (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) (poissonMeasure r) := by
  have hs := integrable_poissonMeasure_iff.mp
    ((_root_.Prove2MeSourceProof.h_db86699b96bdd02e6e9ffb79 r).add (integrable_const (1 : ℝ)))
  rw [integrable_poissonMeasure_iff, ← summable_nat_add_iff 1]
  refine (hs.mul_left (r : ℝ)).congr fun n ↦ ?_
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

end ProbabilityTheory


