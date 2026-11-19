-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_GronwallIntegral_F000
-- name    : LevyStochCalc_Analysis_GronwallIntegral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:15:18.30416+00:00
-- url     : https://prove2.me/theorems/09a41366-a1cb-45e8-986e-663aa593ed93
-- title:
--   Source declarations: LevyStochCalc.Analysis.GronwallIntegral
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Analysis.GronwallIntegral. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_a7bac1943e88fe21db7cf8b7
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A Grönwall inequality in integral form

A nonnegative function bounded by a multiple of its own running integral is identically zero:
iterating the inequality bounds it by `B·(c(t−a))ᵐ/m!` for every `m`, and that tends to zero.
-/

open MeasureTheory

namespace LevyStochCalc.Analysis

/-- **Grönwall in integral form.** A nonnegative function measurable on `Set.Icc a b`, bounded
there and dominated there by a constant multiple of its own running integral, vanishes. -/
theorem eq_zero_of_le_mul_setIntegral {a b c B : ℝ} (hc : 0 ≤ c)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hf0 : ∀ t, 0 ≤ f t)
    (hB : ∀ t ∈ Set.Icc a b, f t ≤ B)
    (hineq : ∀ t ∈ Set.Icc a b, f t ≤ c * ∫ u in Set.Ioc a t, f u) :
    ∀ t ∈ Set.Icc a b, f t = 0 := by
  intro t ht
  refine le_antisymm ?_ (hf0 t)
  have hlim : Filter.Tendsto (fun m : ℕ => B * ((c * (t - a)) ^ m / (m).factorial))
      Filter.atTop (nhds 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (c * (t - a))).const_mul B
  refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun m => ?_)
  calc f t ≤ B * (c * (t - a)) ^ m / (m).factorial :=
        _root_.Prove2MeSourceProof.h_a7bac1943e88fe21db7cf8b7 hc hf hf0 hB hineq m t ht
    _ = B * ((c * (t - a)) ^ m / (m).factorial) := by ring
end LevyStochCalc.Analysis


