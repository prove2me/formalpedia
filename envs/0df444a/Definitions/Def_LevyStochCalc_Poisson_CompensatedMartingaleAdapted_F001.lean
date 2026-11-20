-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001
-- name    : LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:58:56.417602+00:00
-- url     : https://prove2.me/theorems/7c1568ea-154d-45f1-832a-c11548e69dda
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedMartingaleAdapted
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedMartingaleAdapted. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Definitions.Def_SourceProof_1b57c1116b3f8ea72ca9d7fe
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingale property of the simple compensated-Poisson integral

`simpleIntegral N φ` is adapted to a Poisson filtration `ℱ` of `N`: each time-rectangle
`timeRect i t` lies in the past `Iic t ×ˢ univ`, so its compensated mass is `ℱ_t`-measurable,
and the coefficient `ξᵢ` is `ℱ_t`-measurable once `t` reaches the partition point (the term
vanishing before). Each summand is `P`-integrable, its conditional expectation satisfies
`𝔼[ξᵢ·Ñ(timeRect i t) | ℱ_s] =ᵐ ξᵢ·Ñ(timeRect i s)` for `0 ≤ s ≤ t`, and summing over the
partition gives the martingale property of `t ↦ simpleIntegral N φ t`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Conditional mean-zero of a time-rectangle increment `(a, b] ×ˢ A`** whose
lower endpoint dominates the conditioning time when non-degenerate. Degenerate
(`a = b`) increments are `0`; for `a = s` it is the base future increment; for
`s < a` the tower property reduces it to the base case at `ℱ_a`. -/
lemma compensated_condExp_Ioc_eq_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {s a b : ℝ} (hs : 0 ≤ s) (hab : a ≤ b) (hlow : a < b → s ≤ a)
    {A : Set E} (hA : MeasurableSet A) (hA_fin : ν A ≠ ⊤) :
    P[fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω
        | ℱ s]
      =ᵐ[P] fun _ => (0 : ℝ) := by
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · have hemp : (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) = fun _ => (0 : ℝ) := by
      funext ω
      rw [← hab_eq, Set.Ioc_self, Set.empty_prod]
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp
    rw [hemp]
    exact Filter.EventuallyEq.of_eq
      (MeasureTheory.condExp_const (ℱ.le' s) (0 : ℝ))
  · have hsa := hlow hab_lt
    rcases eq_or_lt_of_le hsa with hsa_eq | hsa_lt
    · rw [← hsa_eq]
      exact _root_.Prove2MeSourceProof.h_1b57c1116b3f8ea72ca9d7fe N ℱ hℱ hs (hsa_eq ▸ hab_lt) hA hA_fin
    · have h_base := _root_.Prove2MeSourceProof.h_1b57c1116b3f8ea72ca9d7fe N ℱ hℱ (le_trans hs hsa) hab_lt hA hA_fin
      have hm₂a := ℱ.le' a
      haveI : SigmaFinite (P.trim hm₂a) := inferInstance
      have h_tower := MeasureTheory.condExp_condExp_of_le (μ := P)
        (f := fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω)
        (ℱ.mono hsa) hm₂a
      refine h_tower.symm.trans ((MeasureTheory.condExp_congr_ae h_base).trans ?_)
      exact Filter.EventuallyEq.of_eq
        (MeasureTheory.condExp_const (ℱ.le' s) (0 : ℝ))
/-- **a.e.-additivity of the compensated mass on disjoint finite-intensity sets.**
`Ñ(B ∪ C) =ᵐ Ñ(B) + Ñ(C)`. The reference intensity is a measure (additive
everywhere), and `N(B), N(C)` are a.e. finite (`integer_valued`), so the `toReal`
of the `N`-sum splits a.e. -/
lemma compensated_union_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C)
    (hB_fin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hC_fin : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤) :
    (fun ω => N.compensated (B ∪ C) ω)
      =ᵐ[P] fun ω => N.compensated B ω + N.compensated C ω := by
  filter_upwards [N.integer_valued hB hB_fin, N.integer_valued hC hC_fin] with ω hnB hnC
  obtain ⟨nB, hnB⟩ := hnB
  obtain ⟨nC, hnC⟩ := hnC
  unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
  rw [MeasureTheory.measure_union hBC hC, MeasureTheory.measure_union hBC hC,
    ENNReal.toReal_add (by rw [hnB]; exact ENNReal.natCast_ne_top nB)
      (by rw [hnC]; exact ENNReal.natCast_ne_top nC),
    ENNReal.toReal_add hB_fin hC_fin]
  ring
/-- General finiteness of the reference intensity of a time-rectangle `(a, b] ×ˢ A`
when `A` has finite `ν`-mass. -/
lemma referenceIntensity_Ioc_prod_ne_top
    {ν : Measure E} [SigmaFinite ν] {a b : ℝ} {A : Set E} (hA_fin : ν A ≠ ⊤) :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ := by
  rw [LevyStochCalc.Poisson.referenceIntensity, MeasureTheory.Measure.prod_prod]
  refine ENNReal.mul_ne_top ?_ hA_fin
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_left)
end LevyStochCalc.Poisson.Compensated


