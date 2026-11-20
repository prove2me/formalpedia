-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ChainRule_F001
-- name    : LevyStochCalc_Poisson_ChainRule_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:35:04.539221+00:00
-- url     : https://prove2.me/theorems/21540209-67dc-4b83-9bc0-bf8a90b2046f
-- title:
--   Source declarations: LevyStochCalc.Poisson.ChainRule
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ChainRule. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ChainRule_F000
import Definitions.Def_SourceProof_07135226a3b6eb1d82b734e1
import Definitions.Def_SourceProof_a893600c0517c19e216d57fb

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump chain rule for a Poisson random measure

A product over a finite set whose factors are ordered by a key telescopes: the product minus one
is the sum, over the factors, of the product of the earlier ones times the increment of that
factor. On a set of finite reference intensity a Poisson random measure is a finite sum of unit
masses at distinct times, so the exponential of an integral against it obeys that telescoping,
which is the chain rule the exponential family needs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

section Telescope

variable {α : Type*} [DecidableEq α] {K : Type*} [LinearOrder K] {M : Type*} [CommRing M]

end Telescope

section Pathwise

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

open scoped Classical in
/-- **The jump chain rule for a Poisson random measure of finite intensity.** -/
theorem ae_exp_windowSum_sub_one (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (h : ℝ × E → ℝ) (T : ℝ) :
    ∀ᵐ ω ∂P, Complex.exp (Complex.I * (windowSum N B h T ω : ℂ)) - 1
      = ∫ p in B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ,
          Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
            * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω) := by
  have hRm : MeasurableSet (B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ) :=
    hB.inter (measurableSet_Ioc.prod MeasurableSet.univ)
  have hRfin : referenceIntensity ν (B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  filter_upwards [ae_exists_eq_sum_dirac N hRm hRfin, N.integer_valued hRm hRfin,
    _root_.Prove2MeSourceProof.h_2d4c8b457cb0b7f5fdc2dc58 N hRm hRfin, _root_.Prove2MeSourceProof.h_07135226a3b6eb1d82b734e1 N hB hfin]
    with ω hsrepex hn hIV hsimple
  exact _root_.Prove2MeSourceProof.h_a893600c0517c19e216d57fb N hB h measurableSet_Ioc (fun x hx => hx.1)
    (fun u hu x hx => ⟨hx.1, hx.2.le.trans hu.2⟩) ω hsrepex hn hIV hsimple
/-- Restricting a finite sum of point masses to a measurable subset of its window. -/
theorem restrict_eq_sum_dirac_of_subset {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α} {B R : Set α} (hRm : MeasurableSet R)
    (hRB : R ⊆ B) {s : Finset α}
    (hs : μ.restrict B = ∑ p ∈ s, (μ.restrict B) {p} • Measure.dirac p) :
    μ.restrict R = ∑ p ∈ s, (μ.restrict R) {p} • Measure.dirac p := by
  classical
  ext A hA
  have h1 : (μ.restrict R) A = (μ.restrict B) (A ∩ R) := by
    rw [Measure.restrict_apply hA, Measure.restrict_apply (hA.inter hRm),
      Set.inter_eq_left.mpr (Set.inter_subset_right.trans hRB)]
  rw [h1, hs, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_finsetSum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ (hA.inter hRm),
    Measure.dirac_apply' _ hA, smul_eq_mul, smul_eq_mul,
    Measure.restrict_apply (measurableSet_singleton p),
    Measure.restrict_apply (measurableSet_singleton p)]
  by_cases hpR : p ∈ R
  · rw [Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (hRB hpR)),
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hpR)]
    by_cases hpA : p ∈ A
    · simp [hpA, hpR]
    · simp [hpA]
  · rw [Set.indicator_of_notMem (fun hm => hpR hm.2), Set.singleton_inter_eq_empty.mpr hpR,
      measure_empty, mul_zero, zero_mul]
end Pathwise

end LevyStochCalc.Poisson


