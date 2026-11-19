-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
-- name    : LevyStochCalc_Poisson_Simplicity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:21:26.987801+00:00
-- url     : https://prove2.me/theorems/632e3d7d-f20c-4b3c-b7e0-5dd725f8758e
-- title:
--   Source declarations: LevyStochCalc.Poisson.Simplicity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.Simplicity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ZeroIntensity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time-simplicity of a Poisson random measure on a finite-intensity set

On a set of finite reference intensity the count of a Poisson random measure exceeds one with
probability at most the square of the intensity. The reference intensity is a product with
Lebesgue measure in time, so the masses of the dyadic time slabs of such a set are the integrals
of an integrable density over intervals of vanishing length, and therefore have vanishing
supremum. A union bound then makes the probability that some slab of level `n` carries two or
more points tend to zero, so almost surely no two points share a time and every point is simple.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Tail

/-- The Poisson law of mean `r` puts mass at most `r ^ 2` on the counts of at least two. -/
theorem poissonMeasure_two_le_le (r : ℝ≥0) :
    ProbabilityTheory.poissonMeasure r {n : ℕ | 2 ≤ n} ≤ ENNReal.ofReal ((r : ℝ) ^ 2) := by
  have hms : MeasurableSet ({0, 1} : Set ℕ) :=
    (measurableSet_singleton 0).union (measurableSet_singleton 1)
  have hset : {n : ℕ | 2 ≤ n} = ({0, 1} : Set ℕ)ᶜ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hpair : ProbabilityTheory.poissonMeasure r ({0, 1} : Set ℕ)
      = ENNReal.ofReal (Real.exp (-(r : ℝ)) + Real.exp (-(r : ℝ)) * (r : ℝ)) := by
    rw [Set.insert_eq, measure_union (by simp) (measurableSet_singleton 1),
      ProbabilityTheory.poissonMeasure_singleton, ProbabilityTheory.poissonMeasure_singleton,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num
  have hc0 : (0 : ℝ) ≤ Real.exp (-(r : ℝ)) + Real.exp (-(r : ℝ)) * (r : ℝ) := by positivity
  rw [hset, prob_compl_eq_one_sub hms, hpair, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ hc0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hE : 1 - Real.exp (-(r : ℝ)) ≤ (r : ℝ) := by
    have h := Real.add_one_le_exp (-(r : ℝ))
    linarith
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hE)]
/-- **On a set of finite reference intensity a Poisson random measure carries two or more points
with probability at most the square of the intensity.** -/
theorem measure_two_le_count_le (N : PoissonRandomMeasure.{u, v, w} P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    P {ω | 2 ≤ N.N ω B} ≤ referenceIntensity ν B ^ 2 := by
  have hms : MeasurableSet {x : ℝ≥0∞ | 2 ≤ x} := measurableSet_le measurable_const measurable_id
  have hpre : ((↑) : ℕ → ℝ≥0∞) ⁻¹' {x : ℝ≥0∞ | 2 ≤ x} = {n : ℕ | 2 ≤ n} := by
    ext n
    simp [Set.mem_setOf_eq, Nat.ofNat_le_cast]
  have hlaw := N.poisson_law hB hfin
  have hpush : P {ω | 2 ≤ N.N ω B}
      = ProbabilityTheory.poissonMeasure (referenceIntensity ν B).toNNReal {n : ℕ | 2 ≤ n} := by
    rw [show {ω | 2 ≤ N.N ω B} = (fun ω => N.N ω B) ⁻¹' {x : ℝ≥0∞ | 2 ≤ x} from rfl,
      ← Measure.map_apply (N.measurable_eval hB) hms, hlaw, poissonMeasureENN,
      Measure.map_apply measurable_from_nat hms, hpre]
  rw [hpush]
  refine (poissonMeasure_two_le_le _).trans (le_of_eq ?_)
  rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow,
    ENNReal.coe_toNNReal hfin]
end Tail

section Mesh

/-- The `k`-th dyadic time slab of level `n`. -/
def timeSlab (n k : ℕ) : Set ℝ := Set.Ioc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)
theorem measurableSet_timeSlab (n k : ℕ) : MeasurableSet (timeSlab n k) := measurableSet_Ioc
theorem volume_timeSlab (n k : ℕ) :
    volume (timeSlab n k) = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  rw [timeSlab, Real.volume_Ioc]
  congr 1
  rw [div_sub_div_same, add_sub_cancel_left, div_pow, one_pow]
end Mesh

section Simple

end Simple

end LevyStochCalc.Poisson


