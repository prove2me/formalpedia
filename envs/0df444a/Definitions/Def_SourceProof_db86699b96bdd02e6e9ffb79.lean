-- Prove2me | Definitions.Def_SourceProof_db86699b96bdd02e6e9ffb79
-- name    : SourceProof_db86699b96bdd02e6e9ffb79
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:57:47.332124+00:00
-- url     : https://prove2.me/theorems/ec85eb09-73c9-416d-9ba3-4badfe672653
-- title:
--   StochLean source theorem: ProbabilityTheory.integrable_natCast_poisson

import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Mathlib.Analysis.Calculus.Deriv.Slope

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Interval-count axioms for Poisson processes

This file formalizes Klenke's interval axioms P1--P5 for a counting process.  In addition to
those axioms, the predicate records the design-level path convention used by StochLean: paths are
almost surely monotone and right-continuous on one common event, and the process starts at zero.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


theorem _root_.Prove2MeSourceProof.h_db86699b96bdd02e6e9ffb79 (r : NNReal) :
    Integrable (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff, ← summable_nat_add_iff 1]
  refine ((Real.summable_pow_div_factorial (r : ℝ)).mul_left
      (Real.exp (-(r : ℝ)) * (r : ℝ))).congr fun n ↦ ?_
  simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_factorial, pow_succ]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp
namespace IsPoissonProcess

variable {X : NNReal → Ω → ℕ} {rate : NNReal} {P : Measure Ω} [IsProbabilityMeasure P]

end IsPoissonProcess

end ProbabilityTheory


