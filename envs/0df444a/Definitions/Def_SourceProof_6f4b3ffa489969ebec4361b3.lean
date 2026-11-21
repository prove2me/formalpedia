-- Prove2me | Definitions.Def_SourceProof_6f4b3ffa489969ebec4361b3
-- name    : SourceProof_6f4b3ffa489969ebec4361b3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:32:29.023319+00:00
-- url     : https://prove2.me/theorems/77b0647a-47f7-4525-a444-7d8a2cd257a1
-- title:
--   LevyStochCalc source module: SourceProof_6f4b3ffa489969ebec4361b3
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.weighted_box_cross_disjoint_zero` comes from the `LevyStochCalc.Poisson.CompensatedDensityBoxIsometry` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002
import Definitions.Def_SourceProof_3d2400462fa592bc2611c9ac

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


theorem _root_.Prove2MeSourceProof.h_6f4b3ffa489969ebec4361b3
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hAf : ν A ≠ ⊤) (hA'f : ν A' ≠ ⊤) (hdisjA : Disjoint A A')
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P = 0 := by
  set R := Set.Ioc a b ×ˢ A with hRdef
  set R' := Set.Ioc a b ×ˢ A' with hR'def
  have hRmeas : MeasurableSet R := measurableSet_Ioc.prod hA
  have hR'meas : MeasurableSet R' := measurableSet_Ioc.prod hA'
  have hRf : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hAf
  have hR'f : LevyStochCalc.Poisson.referenceIntensity ν R' ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hA'f
  have hUAf : ν (A ∪ A') ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hAf, hA'f⟩) (measure_union_le A A')
  have hRUeq : R ∪ R' = Set.Ioc a b ×ˢ (A ∪ A') := Set.prod_union.symm
  have hRUf : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∪ A')) ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hUAf
  have hRdisj : Disjoint R R' := Set.disjoint_prod.mpr (Or.inr hdisjA)
  -- a.e. compensated additivity on the disjoint union.
  have hadd_ae : (fun ω => N.compensated (R ∪ R') ω)
      =ᵐ[P] (fun ω => N.compensated R ω + N.compensated R' ω) := by
    filter_upwards [N.integer_valued (hRmeas.union hR'meas) (hRUeq ▸ hRUf)] with ω hω
    obtain ⟨n, hn⟩ := hω
    have hUfin : N.N ω (R ∪ R') ≠ ⊤ := by rw [hn]; exact ENNReal.natCast_ne_top n
    have hRne : N.N ω R ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono Set.subset_union_left)
    have hR'ne : N.N ω R' ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono Set.subset_union_right)
    simp only [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
    rw [show N.N ω (R ∪ R') = N.N ω R + N.N ω R' from measure_union hRdisj hR'meas,
      show LevyStochCalc.Poisson.referenceIntensity ν (R ∪ R')
          = LevyStochCalc.Poisson.referenceIntensity ν R
            + LevyStochCalc.Poisson.referenceIntensity ν R' from measure_union hRdisj hR'meas,
      ENNReal.toReal_add hRne hR'ne, ENNReal.toReal_add hRf hR'f]
    ring
  -- integrability of `g·Ñ(box)²` (bounded weight × square-integrable).
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g P :=
    (hg.mono (ℱ.le' a)).measurable.aestronglyMeasurable
  have hgbnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have hiR : MeasureTheory.Integrable (fun ω => g ω * (N.compensated R ω) ^ 2) P :=
    (_root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hRmeas hRf).bdd_mul hg_aesm hgbnd
  have hiR' : MeasureTheory.Integrable (fun ω => g ω * (N.compensated R' ω) ^ 2) P :=
    (_root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hR'meas hR'f).bdd_mul hg_aesm hgbnd
  have hiU : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (R ∪ R') ω) ^ 2) P :=
    (_root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N (hRmeas.union hR'meas) (hRUeq ▸ hRUf)).bdd_mul hg_aesm hgbnd
  -- pointwise polarisation (a.e., using the additivity).
  have hpt_ae : (fun ω => g ω * (N.compensated R ω * N.compensated R' ω))
      =ᵐ[P] (fun ω => 2⁻¹ * (g ω * (N.compensated (R ∪ R') ω) ^ 2)
          - 2⁻¹ * (g ω * (N.compensated R ω) ^ 2)
          - 2⁻¹ * (g ω * (N.compensated R' ω) ^ 2)) := by
    filter_upwards [hadd_ae] with ω h
    rw [h]; ring
  have hfX : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated (R ∪ R') ω) ^ 2)) P := hiU.const_mul 2⁻¹
  have hfY : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated R ω) ^ 2)) P := hiR.const_mul 2⁻¹
  have hfZ : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated R' ω) ^ 2)) P := hiR'.const_mul 2⁻¹
  have hfXY : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated (R ∪ R') ω) ^ 2)
        - 2⁻¹ * (g ω * (N.compensated R ω) ^ 2)) P := hfX.sub hfY
  rw [MeasureTheory.integral_congr_ae hpt_ae,
    MeasureTheory.integral_sub hfXY hfZ,
    MeasureTheory.integral_sub hfX hfY,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  -- evaluate each weighted square via `weighted_box_sq_eq`.
  rw [show (∫ ω, g ω * (N.compensated (R ∪ R') ω) ^ 2 ∂P)
        = ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ (A ∪ A')) ω) ^ 2 ∂P from by rw [hRUeq],
    _root_.Prove2MeSourceProof.h_3d2400462fa592bc2611c9ac N ℱ hℱ ha hab (hA.union hA') hUAf hg,
    _root_.Prove2MeSourceProof.h_3d2400462fa592bc2611c9ac N ℱ hℱ ha hab hA hAf hg, _root_.Prove2MeSourceProof.h_3d2400462fa592bc2611c9ac N ℱ hℱ ha hab hA' hA'f hg]
  -- `ν̂(R∪R') = ν̂(R)+ν̂(R')` (disjoint) ⇒ the bracket cancels.
  have hrefU : (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∪ A'))).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν R).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν R').toReal := by
    rw [← hRUeq, show LevyStochCalc.Poisson.referenceIntensity ν (R ∪ R')
          = LevyStochCalc.Poisson.referenceIntensity ν R
            + LevyStochCalc.Poisson.referenceIntensity ν R' from measure_union hRdisj hR'meas,
      ENNReal.toReal_add hRf hR'f]
  rw [hrefU]; ring
end LevyStochCalc.Poisson.Compensated


