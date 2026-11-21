-- Prove2me | Definitions.Def_SourceProof_f869d2367bb5fe9e2110213a
-- name    : SourceProof_f869d2367bb5fe9e2110213a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:27:42.499921+00:00
-- url     : https://prove2.me/theorems/d1850e21-6aee-4707-8be6-0e9bf54af8d6
-- title:
--   LevyStochCalc source module: SourceProof_f869d2367bb5fe9e2110213a
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.markSum_cross_timeordered` comes from the `LevyStochCalc.Poisson.CompensatedDensityMarkSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000
import Definitions.Def_SourceProof_0687114e79a04bc113c164e4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_f869d2367bb5fe9e2110213a
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b c d : ℝ} (hc : 0 ≤ c) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ ζ : Fin K → Ω → ℝ)
    (hξb : ∀ k, ∃ M, ∀ ω, |ξ k ω| ≤ M) (hζb : ∀ k, ∃ M, ∀ ω, |ζ k ω| ≤ M)
    (hξm : ∀ k, Measurable (ξ k)) (hζm : ∀ k, Measurable (ζ k))
    (hξadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) (ξ k))
    (hζadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ c) (ζ k)) :
    ∫ ω, (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
        * (∑ l : Fin K, ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω) ∂P = 0 := by
  have hac : a ≤ c := hab.le.trans hbc
  have hBxm : ∀ k, MeasurableSet (Set.Ioc a b ×ˢ B k) := fun k => measurableSet_Ioc.prod (hBm k)
  have hCxm : ∀ l, MeasurableSet (Set.Ioc c d ×ˢ B l) := fun l => measurableSet_Ioc.prod (hBm l)
  have hBxf : ∀ k, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ B k) ≠ ⊤ :=
    fun k => LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top (hBf k)
  have hCxf : ∀ l, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc c d ×ˢ B l) ≠ ⊤ :=
    fun l => LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top (hBf l)
  have hint : ∀ k l, MeasureTheory.Integrable
      (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
        * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω)) P := by
    intro k l
    obtain ⟨Mk, hMk⟩ := hξb k
    obtain ⟨Ml, hMl⟩ := hζb l
    have hcross := _root_.Prove2MeSourceProof.h_839c3c586f330ad57afd5326 N (hBxm k) (hCxm l) (hBxf k) (hCxf l)
    have heq : (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω))
        = (fun ω => (ξ k ω * ζ l ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc c d ×ˢ B l) ω)) := funext (fun ω => by ring)
    rw [heq]
    refine hcross.bdd_mul (c := Mk * Ml) ((hξm k).mul (hζm l)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMk ω) (hMl ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
  rw [show (fun ω => (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (∑ l : Fin K, ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω))
      = fun ω => ∑ k : Fin K, ∑ l : Fin K,
          (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω) from
    funext (fun ω => Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _
      (fun l _ => hint k l))]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun l _ => hint k l)]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  have hgadapt : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq c) (fun ω => ξ k ω * ζ l ω) :=
    ((hξadapt k).mono (ℱ.mono hac)).mul (hζadapt l)
  rw [show (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω))
        = fun ω => (ξ k ω * ζ l ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc c d ×ˢ B l) ω) from funext (fun ω => by ring)]
  exact _root_.Prove2MeSourceProof.h_0687114e79a04bc113c164e4 N ℱ hℱ hc hbc hcd (hBm k) (hBm l) (hBf l) hgadapt
end LevyStochCalc.Poisson.Compensated


