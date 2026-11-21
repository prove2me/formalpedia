-- Prove2me | Definitions.Def_SourceProof_115508132628c570aa207f8e
-- name    : SourceProof_115508132628c570aa207f8e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:11:46.655459+00:00
-- url     : https://prove2.me/theorems/813b1dca-8d48-4719-900c-51936e0126c5
-- title:
--   LevyStochCalc source module: SourceProof_115508132628c570aa207f8e
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.markSum_sq_sametime` comes from the `LevyStochCalc.Poisson.CompensatedDensityMarkSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000
import Definitions.Def_SourceProof_8687c54d9d7241acdf4393bb

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


theorem _root_.Prove2MeSourceProof.h_115508132628c570aa207f8e
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin K → Ω → ℝ) (hξb : ∀ k, ∃ M, ∀ ω, |ξ k ω| ≤ M) (hξm : ∀ k, Measurable (ξ k))
    (hadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) (ξ k)) :
    ∫ ω, (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω) ^ 2 ∂P
      = ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ k ω * ξ k' ω ∂P := by
  have hBxm : ∀ k, MeasurableSet (Set.Ioc a b ×ˢ B k) := fun k => measurableSet_Ioc.prod (hBm k)
  have hBxf : ∀ k, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ B k) ≠ ⊤ :=
    fun k => LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top (hBf k)
  -- integrability of each cross term.
  have hint : ∀ k k', MeasureTheory.Integrable
      (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
        * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω)) P := by
    intro k k'
    obtain ⟨Mk, hMk⟩ := hξb k
    obtain ⟨Mk', hMk'⟩ := hξb k'
    have hcross := _root_.Prove2MeSourceProof.h_839c3c586f330ad57afd5326 N (hBxm k) (hBxm k') (hBxf k) (hBxf k')
    have heq : (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω))
        = (fun ω => (ξ k ω * ξ k' ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc a b ×ˢ B k') ω)) := funext (fun ω => by ring)
    rw [heq]
    refine hcross.bdd_mul (c := Mk * Mk') ((hξm k).mul (hξm k')).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMk ω) (hMk' ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
  rw [show (fun ω => (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω) ^ 2)
      = fun ω => ∑ k : Fin K, ∑ k' : Fin K,
          (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω) from
    funext (fun ω => by rw [sq]; exact Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _
      (fun k' _ => hint k k'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => hint k k')]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  obtain ⟨Mk, hMk⟩ := hξb k
  obtain ⟨Mk', hMk'⟩ := hξb k'
  have hbnd : ∀ ω, |ξ k ω * ξ k' ω| ≤ Mk * Mk' := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hMk ω) (hMk' ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
  have hgadapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) (fun ω => ξ k ω * ξ k' ω) :=
    (hadapt k).mul (hadapt k')
  rw [show (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω))
        = fun ω => (ξ k ω * ξ k' ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc a b ×ˢ B k') ω) from funext (fun ω => by ring),
    _root_.Prove2MeSourceProof.h_8687c54d9d7241acdf4393bb N ℱ hℱ ha hab (hBm k) (hBm k') (hBf k) (hBf k') hgadapt hbnd,
    mul_comm]
end LevyStochCalc.Poisson.Compensated


