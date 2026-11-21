-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000
-- name    : LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:34:39.29853+00:00
-- url     : https://prove2.me/theorems/36aef4fd-181c-44fc-89e9-8245313334a1
-- title:
--   LevyStochCalc source module: LevyStochCalc.Poisson.CompensatedDensityBoxIsometry
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Poisson.CompensatedDensityBoxIsometry in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002
import Definitions.Def_SourceProof_3d2400462fa592bc2611c9ac
import Definitions.Def_SourceProof_6f4b3ffa489969ebec4361b3

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

/-- **Weighted disjoint-difference second moment.** For an `ℱ_a`-measurable bounded
weight `g` and two same-time boxes on disjoint marks `C, D`,
`E[g·(Ñ((a,b]×C) − Ñ((a,b]×D))²] = E[g]·ν̂((a,b]×C) + E[g]·ν̂((a,b]×D)`. Polarisation
expansion: squares via `weighted_box_sq_eq`, cross via `weighted_box_cross_disjoint_zero`. -/
lemma weighted_box_diff_sq_disjoint
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {C D : Set E} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCf : ν C ≠ ⊤) (hDf : ν D ≠ ⊤) (hdisjCD : Disjoint C D)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
        - N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ C)).toReal
        + (∫ ω, g ω ∂P)
          * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ D)).toReal := by
  have hCm : MeasurableSet (Set.Ioc a b ×ˢ C) := measurableSet_Ioc.prod hC
  have hDm : MeasurableSet (Set.Ioc a b ×ˢ D) := measurableSet_Ioc.prod hD
  have hCf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ C) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hCf
  have hDf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ D) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hDf
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g P :=
    (hg.mono (ℱ.le' a)).measurable.aestronglyMeasurable
  have hgbnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have hiC : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω) ^ 2) P :=
    (_root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hCm hCf').bdd_mul hg_aesm hgbnd
  have hiD : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2) P :=
    (_root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hDm hDf').bdd_mul hg_aesm hgbnd
  have hiCD : MeasureTheory.Integrable
      (fun ω => 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
        * N.compensated (Set.Ioc a b ×ˢ D) ω))) P :=
    ((_root_.Prove2MeSourceProof.h_839c3c586f330ad57afd5326 N hCm hDm hCf' hDf').bdd_mul hg_aesm hgbnd).const_mul 2
  have hmid : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω) ^ 2
        - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
          * N.compensated (Set.Ioc a b ×ˢ D) ω))) P := hiC.sub hiCD
  have hpt : (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
        - N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2)
      = (fun ω => (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω) ^ 2
          - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
            * N.compensated (Set.Ioc a b ×ˢ D) ω)))
          + g ω * (N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2) := by
    funext ω; ring
  rw [hpt, MeasureTheory.integral_add hmid hiD,
    MeasureTheory.integral_sub hiC hiCD, MeasureTheory.integral_const_mul,
    _root_.Prove2MeSourceProof.h_6f4b3ffa489969ebec4361b3 N ℱ hℱ ha hab hC hD hCf hDf hdisjCD hg hgb,
    _root_.Prove2MeSourceProof.h_3d2400462fa592bc2611c9ac N ℱ hℱ ha hab hC hCf hg, _root_.Prove2MeSourceProof.h_3d2400462fa592bc2611c9ac N ℱ hℱ ha hab hD hDf hg]
  ring
end LevyStochCalc.Poisson.Compensated


