-- Prove2me | Definitions.Def_SourceProof_cee30bfb9b70a700a473aa9b
-- name    : SourceProof_cee30bfb9b70a700a473aa9b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:53:34.846579+00:00
-- url     : https://prove2.me/theorems/100a79aa-a73d-492f-9c6b-ce8efc3d15b2
-- title:
--   LevyStochCalc source module: SourceProof_cee30bfb9b70a700a473aa9b
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.lintegral_enorm_le_energy` comes from the `LevyStochCalc.Poisson.CompensatorL1` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensator_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From energy to the mean pathwise integral

The compensator identity turns the mean of the absolute integral against the random measure into
the mean against the reference intensity, and on a window of finite intensity the latter is
controlled by the energy through the comparison of `L¹` with `L²`. So an energy-null sequence of
predictable marked integrands has pathwise compensated integrals tending to zero in mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Bound

variable {A : Set E} {T : ℝ}

omit [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_cee30bfb9b70a700a473aa9b (hRfin : referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤)
    {η : Ω → ℝ → E → ℝ} (hη : Measurable fun p : Ω × ℝ × E => η p.1 p.2.1 p.2.2) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P
      ≤ (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            ‖η ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P) ^ (2 : ℝ)⁻¹
        * referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ^ (2 : ℝ)⁻¹ := by
  set R : Set (ℝ × E) := Set.Ioc (0 : ℝ) T ×ˢ A with hRdef
  haveI hfin : IsFiniteMeasure ((LevyStochCalc.Poisson.referenceIntensity ν).restrict R) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hRfin
  set Λ : Measure (Ω × ℝ × E) := P.prod ((LevyStochCalc.Poisson.referenceIntensity ν).restrict R) with hΛ
  set f : Ω × ℝ × E → ℝ := fun p => η p.1 p.2.1 p.2.2 with hf
  have hΛuniv : Λ Set.univ = LevyStochCalc.Poisson.referenceIntensity ν R := by
    rw [hΛ, ← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, measure_univ,
      one_mul]
  have hone : ∫⁻ p, ‖f p‖ₑ ∂Λ
      = ∫⁻ ω, ∫⁻ q in R, ‖η ω q.1 q.2‖ₑ ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P := by
    rw [hΛ, lintegral_prod _ (hη.enorm.aemeasurable)]
  have htwo : ∫⁻ p, ‖f p‖ₑ ^ 2 ∂Λ
      = ∫⁻ ω, ∫⁻ q in R, ‖η ω q.1 q.2‖ₑ ^ 2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P := by
    rw [hΛ, lintegral_prod _ ((hη.enorm.pow_const 2).aemeasurable)]
  have hL2 : eLpNorm f 2 Λ = (∫⁻ p, ‖f p‖ₑ ^ 2 ∂Λ) ^ (2 : ℝ)⁻¹ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := Λ) (f := f)
    (p := 1) (q := 2) (by norm_num) hη.stronglyMeasurable.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm, hL2, hΛuniv] at hcmp
  rw [← hone, ← htwo]
  refine hcmp.trans (le_of_eq ?_)
  norm_num
end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}

end Pathwise

end LevyStochCalc.Poisson


