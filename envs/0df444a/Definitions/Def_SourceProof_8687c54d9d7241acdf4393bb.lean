-- Prove2me | Definitions.Def_SourceProof_8687c54d9d7241acdf4393bb
-- name    : SourceProof_8687c54d9d7241acdf4393bb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:24:47.171593+00:00
-- url     : https://prove2.me/theorems/5026cd4d-efd4-4141-ac04-418ed98c45fb
-- title:
--   LevyStochCalc source module: SourceProof_8687c54d9d7241acdf4393bb
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.weighted_box_cross_sametime` comes from the `LevyStochCalc.Poisson.CompensatedDensityBoxIsometry` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000
import Definitions.Def_SourceProof_555e93e74cc0dd7d3e1f7b7a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted covariances of compensated boxes

Second moments and cross moments of compensated masses `Ñ((a,b] × A)` weighted by a
past-measurable factor: the weighted second moment, vanishing of the cross terms for disjoint
marks and for time-ordered boxes, and the same-time bilinear covariance in the marks. These
combine into the isometry for a single time interval carrying several marks.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_8687c54d9d7241acdf4393bb
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hAf : ν A ≠ ⊤) (hA'f : ν A' ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P
      = (∫ ω, g ω ∂P)
        * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal := by
  have hAm : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hA'm : MeasurableSet (Set.Ioc a b ×ˢ A') := measurableSet_Ioc.prod hA'
  have hAf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hAf
  have hA'f' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A') ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hA'f
  have hmcf : ν (A \ A') ≠ ⊤ := ne_top_of_le_ne_top hAf (measure_mono Set.sdiff_subset)
  have hmdf : ν (A' \ A) ≠ ⊤ := ne_top_of_le_ne_top hA'f (measure_mono Set.sdiff_subset)
  have hmif : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A')) ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top (ne_top_of_le_ne_top hAf (measure_mono
      Set.inter_subset_left))
  have hmcf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A \ A')) ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hmcf
  have hmdf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A' \ A)) ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hmdf
  -- box set identities.
  have hBdiff : Set.Ioc a b ×ˢ A \ Set.Ioc a b ×ˢ A' = Set.Ioc a b ×ˢ (A \ A') := by
    ext ⟨x, e⟩; simp only [Set.mem_sdiff, Set.mem_prod]; tauto
  have hBa'diff : Set.Ioc a b ×ˢ A' \ Set.Ioc a b ×ˢ A = Set.Ioc a b ×ˢ (A' \ A) := by
    ext ⟨x, e⟩; simp only [Set.mem_sdiff, Set.mem_prod]; tauto
  have hBinter : Set.Ioc a b ×ˢ A ∩ Set.Ioc a b ×ˢ A' = Set.Ioc a b ×ˢ (A ∩ A') := by
    ext ⟨x, e⟩; simp only [Set.mem_inter_iff, Set.mem_prod]; tauto
  -- a.e. `Ñ(R) − Ñ(R') = Ñ((a,b]×(A∖A')) − Ñ((a,b]×(A'∖A))`.
  have hsub_ae : (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω)
      =ᵐ[P] (fun ω => N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
        - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω) := by
    filter_upwards [_root_.Prove2MeSourceProof.h_555e93e74cc0dd7d3e1f7b7a N hAm hA'm hAf',
      _root_.Prove2MeSourceProof.h_555e93e74cc0dd7d3e1f7b7a N hA'm hAm hA'f'] with ω h1 h2
    rw [h1, h2, Set.inter_comm (Set.Ioc a b ×ˢ A') (Set.Ioc a b ×ˢ A), hBdiff, hBa'diff]
    ring
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g P :=
    (hg.mono (ℱ.le' a)).measurable.aestronglyMeasurable
  have hgbnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  -- `∫ g·(Ñ(R)−Ñ(R'))²` via the weighted disjoint-difference value.
  have hsq_ae : (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2)
      =ᵐ[P] (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
        - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω) ^ 2) :=
    hsub_ae.mono (fun ω h => by
      change g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
          - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2
        = g ω * (N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
          - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω) ^ 2
      rw [show N.compensated (Set.Ioc a b ×ˢ A) ω - N.compensated (Set.Ioc a b ×ˢ A') ω
          = N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
            - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω from h])
  have hsq_eq : ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν
            (Set.Ioc a b ×ˢ (A \ A'))).toReal
        + (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν
            (Set.Ioc a b ×ˢ (A' \ A))).toReal :=
    (MeasureTheory.integral_congr_ae hsq_ae).trans
      (LevyStochCalc.Poisson.Compensated.weighted_box_diff_sq_disjoint N ℱ hℱ ha hab (hA.diff hA') (hA'.diff hA) hmcf hmdf
        disjoint_sdiff_sdiff hg hgb)
  -- weighted polarisation expansion (cross term left symbolic).
  have hexp : ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal
        - 2 * (∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
            * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P)
        + (∫ ω, g ω ∂P)
          * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A')).toReal := by
    have hiA : MeasureTheory.Integrable
        (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2) P :=
      (_root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hAm hAf').bdd_mul hg_aesm hgbnd
    have hiA' : MeasureTheory.Integrable
        (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2) P :=
      (_root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hA'm hA'f').bdd_mul hg_aesm hgbnd
    have hicross : MeasureTheory.Integrable
        (fun ω => 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
          * N.compensated (Set.Ioc a b ×ˢ A') ω))) P :=
      ((_root_.Prove2MeSourceProof.h_839c3c586f330ad57afd5326 N hAm hA'm hAf' hA'f').bdd_mul hg_aesm hgbnd).const_mul 2
    have hmid : MeasureTheory.Integrable
        (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2
          - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
            * N.compensated (Set.Ioc a b ×ˢ A') ω))) P := hiA.sub hicross
    rw [show (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
            - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2)
          = fun ω => (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2
            - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
              * N.compensated (Set.Ioc a b ×ˢ A') ω)))
            + g ω * (N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2 from funext (fun ω => by ring),
      MeasureTheory.integral_add hmid hiA', MeasureTheory.integral_sub hiA hicross,
      MeasureTheory.integral_const_mul,
      _root_.Prove2MeSourceProof.h_3d2400462fa592bc2611c9ac N ℱ hℱ ha hab hA hAf hg, _root_.Prove2MeSourceProof.h_3d2400462fa592bc2611c9ac N ℱ hℱ ha hab hA' hA'f hg]
  -- intensity inclusion–exclusion (in `toReal`).
  have hrefBa : (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A \ A'))).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)
          = LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A ∩ Set.Ioc a b ×ˢ A')
            + LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A \ Set.Ioc a b ×ˢ A')
          from (measure_inter_add_sdiff _ hA'm).symm,
      hBinter, hBdiff, ENNReal.toReal_add hmif hmcf']
  have hrefBa' : (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A')).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A' \ A))).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A')
          = LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A' ∩ Set.Ioc a b ×ˢ A)
            + LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A' \ Set.Ioc a b ×ˢ A)
          from (measure_inter_add_sdiff _ hAm).symm,
      Set.inter_comm (Set.Ioc a b ×ˢ A') (Set.Ioc a b ×ˢ A), hBinter, hBa'diff,
      ENNReal.toReal_add hmif hmdf']
  have key := hsq_eq.symm.trans hexp
  rw [hrefBa, hrefBa'] at key
  linear_combination (1 / 2 : ℝ) * key
end LevyStochCalc.Poisson.Compensated


