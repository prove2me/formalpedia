-- Prove2me | Definitions.Def_OAIQ091C009
-- name    : OAIQ091C009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:56:42.531909+00:00
-- url     : https://prove2.me/theorems/06a1081b-7652-48b4-8af1-d9460beffc8d
-- title:
--   Definitions bundle OAIQ091C009 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 178 declarations of OpenAI's Lean: 27 definitions and 151 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.curvatureEulerDensity`, `OAI.PositiveEinsteinFour.Geometry.euclideanHausdorffFactor`, `OAI.PositiveEinsteinFour.Geometry.heatSignedGram`, `OAI.PositiveEinsteinFour.Geometry.hodgeStarFour`, `OAI.PositiveEinsteinFour.Geometry.oneFormConnectionCurvatureMatrix`, `OAI.PositiveEinsteinFour.Geometry.riemannianChartFactor`, `OAI.PositiveEinsteinFour.Geometry.scalarAdjointDrift`, `OAI.PositiveEinsteinFour.Geometry.scalarAdjointFirstL2Term`, `OAI.PositiveEinsteinFour.Geometry.scalarAdjointFirstPiece`, `OAI.PositiveEinsteinFour.Geometry.scalarAdjointL2Perturbation`, `OAI.PositiveEinsteinFour.Geometry.scalarAdjointPotential`, `OAI.PositiveEinsteinFour.Geometry.scalarAdjointSecondL2Term`, `OAI.PositiveEinsteinFour.Geometry.scalarAdjointSecondPiece`, `OAI.PositiveEinsteinFour.Geometry.scalarFormalAdjointOperator`, `OAI.PositiveEinsteinFour.Geometry.scalarIntegerBesselInverse`, `OAI.PositiveEinsteinFour.Geometry.scalarNestedBumpSchwartz`, `OAI.PositiveEinsteinFour.Geometry.scalarNestedRealBump`, `OAI.PositiveEinsteinFour.Geometry.scalarPerturbedCutoffCommutator`, `OAI.PositiveEinsteinFour.Geometry.scalarPerturbedOperator`, `OAI.PositiveEinsteinFour.Geometry.scalarSchwartzDirectOperator`, `OAI.PositiveEinsteinFour.Geometry.scalarSchwartzTranspose`, `OAI.PositiveEinsteinFour.Geometry.twoFormExteriorTensor`, `OAI.PositiveEinsteinFour.Geometry.twoFormSecondTrace`, `OAI.PositiveEinsteinFour.QuaternionFrame.pfaffianFour`, `OAI.PositiveEinsteinFour.QuaternionFrame.upperSquareFour`, `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On`, `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_SupportedH1`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_EuclideanHausdorffFactor`, `EinsteinFour_FourHeatGaussian`, `EinsteinFour_FourHeatGaussianApproximation`, `EinsteinFour_FourHeatGaussianConvolution`, `EinsteinFour_FourHeatGaussianMoments`, `EinsteinFour_FourHeatGaussianSquare`, `EinsteinFour_FourHeatGaussianTimeRegularity`, `EinsteinFour_GeodesicGeometry04`, `EinsteinFour_GeodesicGeometry05`, `EinsteinFour_HodgeTheory08`, `EinsteinFour_MetricQuadraticPerturbation`, `EinsteinFour_RiemannianVolumeFinite`, `EinsteinFour_ScalarAdjointCoordinates`, `EinsteinFour_ScalarAdjointTests`, `EinsteinFour_ScalarEigenMultiplier`, `EinsteinFour_ScalarFullBallIntegerGain`, `EinsteinFour_ScalarHomogeneousInteger`, `EinsteinFour_ScalarPoissonKernelAdjoint`, `EinsteinFour_ScalarPoissonKernelAdjointEstimate`, `EinsteinFour_ScalarPoissonKernelBesselEstimate`, `EinsteinFour_ScalarPoissonKernelBootstrap`, `EinsteinFour_ScalarPoissonKernelCommutator`, `EinsteinFour_ScalarPoissonKernelCutoffs`, `EinsteinFour_ScalarPoissonKernelDerivative`, `EinsteinFour_ScalarPoissonKernelLocalRegularity`, `EinsteinFour_ScalarPoissonKernelLocalRepresentative`, `EinsteinFour_ScalarPoissonKernelLocalization`, `EinsteinFour_ScalarPoissonKernelMultiplier`, `EinsteinFour_ScalarPoissonKernelPerturbation`, `EinsteinFour_ScalarPoissonKernelPotential`, `EinsteinFour_ScalarPoissonKernelSobolev`, `EinsteinFour_ScalarPoissonKernelUniqueness`, `EinsteinFour_ScalarRegularity07`, `EinsteinFour_WeylEstimates03`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C000`, `OAIQ091C001` and `OAIQ091C002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C014` and `OAIQ091C015`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C000
import Definitions.Def_OAIQ091C001
import Definitions.Def_OAIQ091C002

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: smoothing setup (Euclidean)

This file provides the basic “extend by zero + smooth by convolution” infrastructure used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.extendByZeroL2`:
  extend `u : L²(volume.restrict K)` by zero to an element of `L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothL2`:
  a smoothing operator obtained by convolution with a compactly supported continuous kernel `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {K : Set E}

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpace_solutions_1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpace_solutions_1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpace_solutions_1
local instance instMeasurableAdd_solutions_1_r9eac31_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
lemma extendByZeroL2_eq_extendByZeroₗᵢ (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    extendByZeroL2 (E := E) (K := K) hKm u =
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  refine MeasureTheory.Lp.ext ?_
  have h1 :
      (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u :=
    extendByZeroL2_ae_eq (E := E) (K := K) hKm u
  have h2 :
      ((MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u := by
    simp [extendByZeroFun]
    exact
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := (volume : Measure E)) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (s := K) hKm u)
  exact h1.trans h2.symm

lemma norm_extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  calc
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ =
        ‖(MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
          (s := K) hKm) u‖ := by
          simp [extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u]
    _ = ‖u‖ :=
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm).norm_map u
end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: transfer from `BCF` compactness to `L²` (Euclidean)

This file transfers the Arzelà–Ascoli compactness of the `BoundedContinuousFunction` packaging of
`smoothFun` on the compact set `K + tsupport ψ` to a compactness statement in `L²(volume)`.

## Main results

- `smoothL2_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothL2 ψ u | ‖u‖ ≤ R }` has compact closure in `L²(volume)`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.2`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {K : Set E} {ψ : E → ℝ}

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceE_L2CompactnessTransfer
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceE_L2CompactnessTransfer
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceE_L2CompactnessTransfer
local instance instMeasurableAddE_L2CompactnessTransfer_r9eac31_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessTransfer_r9eac31_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
theorem smoothL2_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R)) := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let s : Set E := Kψ (K := K) (ψ := ψ)
  have hs_compact : IsCompact s := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hs : MeasurableSet s := hs_compact.measurableSet
  have hs_lt_top : (volume : Measure E) s < ∞ :=
    hs_compact.measure_lt_top (μ := (volume : Measure E))
  let μs : Measure E := (volume : Measure E).restrict s
  haveI : Fact ((volume : Measure E) s < ∞) := ⟨hs_lt_top⟩
  haveI : IsFiniteMeasure μs := by
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let mS : ℝ := (MeasureTheory.measureUnivNNReal μs) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hmS : 0 ≤ mS := by
    have : 0 ≤ (MeasureTheory.measureUnivNNReal μs) := by simp
    exact Real.rpow_nonneg this _
  let U : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :=
    Metric.closedBall (0 : _) R
  let A :
      Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' U
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' U
  have hA_compact : IsCompact (closure A) :=
    smoothBCF_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hdist_smoothL2_le :
      ∀ u v : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
        dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v) ≤
          mS *
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v) := by
    intro u v
    set Su :=
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
    set Sv :=
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v
    set Bu :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u
    set Bv :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v
    have hBuBv : 0 ≤ ‖Bu - Bv‖ := norm_nonneg _
    -- Work on `F := Su - Sv` and restrict to the finite-measure set `s`.
    let F : (E →₂[(volume : Measure E)] ℝ) := Su - Sv
    let g : E → ℝ := fun x => (F : E → ℝ) x
    have hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (volume : Measure E) := MeasureTheory.Lp.memLp F
    have hg_restrict : MeasureTheory.MemLp g (2 : ℝ≥0∞) μs := hg.restrict s
    let Fs : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μs := hg_restrict.toLp g
    -- Show `Fs` is pointwise bounded by `‖Bu - Bv‖` on `μs`.
    have hF_ae :
        (g =ᵐ[μs] fun x : E =>
          smoothFun (E := E) (K := K) ψ u x -
            smoothFun (E := E) (K := K) ψ v x) := by
      have hsub :
          (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
        simpa [F, g, Su, Sv] using
          (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
      have hu :
          (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
      have hv :
          (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
      have hF :
          (F : E → ℝ) =ᵐ[(volume : Measure E)]
            fun x : E =>
              smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
        exact hsub.trans (hu.sub hv)
      exact MeasureTheory.ae_restrict_of_ae (μ := (volume : Measure E)) (s := s) hF
    have hFs_ae : ((Fs : E → ℝ) =ᵐ[μs] g) := by
      simpa [Fs, g] using
        (MeasureTheory.MemLp.coeFn_toLp (μ := μs) (p := (2 : ℝ≥0∞)) (f := g) hg_restrict)
    have hbound :
        ∀ᵐ x ∂μs, ‖Fs x‖ ≤ ‖Bu - Bv‖ := by
      have hpoint :
          ∀ x : E, x ∈ s → ‖smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x‖ ≤
            ‖Bu - Bv‖ := by
        intro x hx
        let x' : ↥(Kψ (K := K) (ψ := ψ)) := ⟨x, hx⟩
        have hBu : Bu x' = smoothFun (E := E) (K := K) ψ u x := by
          simp [Bu, x']
        have hBv : Bv x' = smoothFun (E := E) (K := K) ψ v x := by
          simp [Bv, x']
        have : ‖(Bu - Bv) x'‖ ≤ ‖Bu - Bv‖ :=
          (Bu - Bv).norm_coe_le_norm x'
        simpa [hBu, hBv] using this
      filter_upwards
        [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hs,
          hFs_ae, hF_ae] with x hx hFs hF
      have := hpoint x hx
      -- rewrite through the AE equalities
      simpa [hFs, hF] using this
    have hnorm_Fs : ‖Fs‖ ≤ mS * ‖Bu - Bv‖ := by
      have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := μs) (p := (2 : ℝ≥0∞))
        (f := Fs) (hC := hBuBv) hbound)
      simpa [mS] using this
    -- Relate the `L²` norm on `volume` to the restricted norm on `μs` using extension-by-zero.
    have hsupport :
        ∀ x : E, x ∉ s →
          smoothFun (E := E) (K := K) ψ u x -
            smoothFun (E := E) (K := K) ψ v x = 0 := by
      intro x hx
      have hu_supp : Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ s := by
        exact
          (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) u)
      have hv_supp : Function.support (smoothFun (E := E) (K := K) ψ v) ⊆ s := by
        exact
          (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) v)
      have hu0 : smoothFun (E := E) (K := K) ψ u x = 0 := by
        have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ u) := fun hx' => hx (hu_supp hx')
        simpa [Function.support] using this
      have hv0 : smoothFun (E := E) (K := K) ψ v x = 0 := by
        have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ v) := fun hx' => hx (hv_supp hx')
        simpa [Function.support] using this
      simp [hu0, hv0]
    have hF0 :
        ∀ᵐ x ∂(volume : Measure E), x ∉ s → g x = 0 := by
      have hF_ae_full :
          (g =ᵐ[(volume : Measure E)]
            fun x : E =>
              smoothFun (E := E) (K := K) ψ u x -
                smoothFun (E := E) (K := K) ψ v x) := by
        have hsub :
            (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
          simpa [F, g, Su, Sv] using
            (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
        have hu :
            (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
          smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
        have hv :
            (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
          smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
        have hF :
            (F : E → ℝ) =ᵐ[(volume : Measure E)]
              fun x : E =>
                smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
          exact hsub.trans (hu.sub hv)
        simpa [g] using hF
      filter_upwards [hF_ae_full] with x hx
      intro hxnot
      have : smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x = 0 :=
        hsupport x hxnot
      simpa [hx] using this
    have hF_ind :
        (s.indicator g =ᵐ[(volume : Measure E)] g) := by
      filter_upwards [hF0] with x hx
      by_cases hxmem : x ∈ s
      · simp [g, hxmem]
      · have : g x = 0 := hx hxmem
        simp [g, hxmem, this]
    -- Conclude `‖F‖ = ‖Fs‖` using `extendByZeroₗᵢ` and the indicator identity.
    let Fext :
        MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E) :=
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := s) hs) Fs
    have hFext_ae :
        ((Fext : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E)) :
            E → ℝ) =ᵐ[(volume : Measure E)]
          s.indicator fun x : E => (Fs : E → ℝ) x := by
      simpa [Fext] using
        (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
          (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := s) hs Fs)
    have hFs_on :
        ∀ᵐ x ∂(volume : Measure E), x ∈ s → (Fs : E → ℝ) x = g x := by
      -- rewrite the AE equality `Fs = g` on the restricted measure as an implication on `volume`
      have := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure E)) (s := s) hs).1 hFs_ae
      simpa [g] using this
    have hindicator :
        (s.indicator (fun x : E => (Fs : E → ℝ) x) =ᵐ[(volume : Measure E)] s.indicator g) := by
      filter_upwards [hFs_on] with x hx
      by_cases hxmem : x ∈ s
      · simp [hxmem, hx hxmem]
      · simp [hxmem]
    have hFext_ae' :
        (Fext : E → ℝ) =ᵐ[(volume : Measure E)] g := by
      exact hFext_ae.trans (hindicator.trans hF_ind)
    have hFext_eq : Fext = F := by
      refine MeasureTheory.Lp.ext ?_
      simpa [g, F] using hFext_ae'
    have hnorm_F : ‖F‖ ≤ mS * ‖Bu - Bv‖ := by
      -- use `‖F‖ = ‖Fs‖` via the isometry.
      have hnorm_ext : ‖Fext‖ = ‖Fs‖ := by
        simp [Fext]
      -- `Fext = F` and `Fs` is bounded.
      have : ‖Fext‖ ≤ mS * ‖Bu - Bv‖ := by
        simpa [hnorm_ext] using hnorm_Fs
      simpa [hFext_eq] using this
    -- Convert to the `dist` statement.
    simpa [Su, Sv, Bu, Bv, F, dist_eq_norm, mS, mul_assoc] using hnorm_F
  have hTB_B : TotallyBounded B := by
    -- Use a finite `BCF` ε-net for `A` with centers in the image, then transfer to `L²`.
    rw [Metric.totallyBounded_iff]
    intro ε hε
    by_cases hmS0 : mS = 0
    ·
      let c : (E →₂[(volume : Measure E)] ℝ) :=
        smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (0 : _)
      refine ⟨{c}, by simp [c], ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hle :=
        hdist_smoothL2_le u (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
      have hdist0 :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              c = 0 := by
        have :
            dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) c ≤ 0 := by
          simpa [c, hmS0] using hle
        exact le_antisymm this dist_nonneg
      refine mem_iUnion.2 ?_
      refine ⟨c, mem_iUnion.2 ?_⟩
      refine ⟨by simp, ?_⟩
      -- membership in the open ball follows from `dist = 0` and `ε > 0`
      simpa [Metric.mem_ball, hdist0] using hε
    · have hmSpos : 0 < mS := lt_of_le_of_ne hmS (Ne.symm hmS0)
      let δ : ℝ := ε / mS
      have hδpos : 0 < δ := div_pos hε hmSpos
      obtain ⟨t, htAsub, htFin, htCover⟩ :=
        exists_finite_cover_balls_of_isCompact_closure (s := A) (ε := δ) hA_compact hδpos
      let tFin : Finset (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
        htFin.toFinset
      have htFin_mem :
          ∀ {f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ}, f ∈ tFin ↔ f ∈ t := by
        intro f
        simp [tFin, htFin.mem_toFinset (a := f)]
      let ι : Type _ := { f // f ∈ tFin }
      have hrep :
          ∀ f : ι,
            ∃ u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
              u ∈ U ∧
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u = f.1 := by
        intro f
        have hf_t : f.1 ∈ t := (htFin_mem (f := f.1)).1 f.2
        have hfA : f.1 ∈ A := htAsub hf_t
        rcases hfA with ⟨u, huU, huEq⟩
        exact ⟨u, huU, huEq⟩
      choose uOf huOfU huOfEq using hrep
      let tL2 : Set (E →₂[(volume : Measure E)] ℝ) :=
        Set.range fun f : ι => smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f)
      have htL2_fin : tL2.Finite := Set.finite_range _
      refine ⟨tL2, htL2_fin, ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hBu : (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) ∈ A := by
        exact ⟨u, huU, rfl⟩
      have : smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u ∈ ⋃ x ∈ t, Metric.ball x δ :=
        htCover hBu
      rcases mem_iUnion.1 this with ⟨f, hf⟩
      rcases mem_iUnion.1 hf with ⟨hf_t, hf_ball⟩
      have hf_tFin : f ∈ tFin := (htFin_mem (f := f)).2 hf_t
      let f' : ι := ⟨f, hf_tFin⟩
      have hf_ball' :
          dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) f < δ := hf_ball
      have hdist :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f')) < ε := by
        have hle := hdist_smoothL2_le u (uOf f')
        have hf_eq :
            smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f') = f := by
          simpa [f'] using huOfEq f'
        have hdist' :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < δ := by
          simpa [hf_eq] using hf_ball'
        have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < ε := by
          have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                  (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < mS * δ := by
            exact mul_lt_mul_of_pos_left hdist' hmSpos
          have hmul : mS * δ = ε := by
            have hmS_ne : mS ≠ 0 := ne_of_gt hmSpos
            calc
              mS * δ = mS * (ε / mS) := by simp [δ]
              _ = mS * ε / mS := (mul_div_assoc mS ε mS).symm
              _ = ε := by simpa using (mul_div_cancel_left₀ ε hmS_ne)
          simpa [hmul] using this
        exact lt_of_le_of_lt hle this
      refine mem_iUnion.2 ?_
      refine ⟨smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f'), ?_⟩
      refine mem_iUnion.2 ?_
      refine ⟨?_, hdist⟩
      -- show the chosen center lies in `tL2`
      exact ⟨f', rfl⟩
  -- Compactness follows from total boundedness + completeness of `L²`.
  have hTB_closure : TotallyBounded (closure B) := hTB_B.closure
  have hcomplete : IsComplete (closure B) := isClosed_closure.isComplete
  have hcompact_closure : IsCompact (closure B) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨hTB_closure, hcomplete⟩
  simpa [B, U] using hcompact_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: Fréchet–Kolmogorov (Euclidean, compact support case)

This file packages the final “precompactness via smoothing” step behind the Euclidean `L²`
compactness criterion used by the Rellich–Kondrachov stack:

- the **smoothing operator** `smoothL2 ψ` has compact image on `Metric.closedBall 0 R`;
- the **approximation inequality** bounds `‖smoothL2 ψ u - extendByZeroL2 u‖` by a translation
  error.

We state the criterion at the level needed by the project: families of `L²` functions with common
compact support (modeled as `Lp ℝ 2 (volume.restrict K)` and embedded into `L²(volume)` via
`extendByZeroL2`).

## Main results

- `norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le`:
  if the translation error averaged against `kernelMeasure ψ` is ≤ `η²`, then smoothing approximates
  `extendByZeroL2` within `η`.
- `totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  if a bounded family admits, at every scale `ε`, a kernel `ψ` for which the above translation error
  is uniformly small, then the embedded family is totally bounded in `L²(volume)`.
- `isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  the corresponding compact-closure statement.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.3`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {K : Set E} {ψ : E → ℝ}

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceE_L2CompactnessFrechetKolmogorov
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceE_L2CompactnessFrechetKolmogorov
local instance instOpensMeasurableSpaceE_L2CompactnessFrechetKolmogorov_r9eac31_1 :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddE_L2CompactnessFrechetKolmogorov_r9eac31_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_L2CompactnessFrechetKolmogorov_r9eac31_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
theorem totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) := by
  classical
  -- Use the finite `ε`-net characterization of total boundedness.
  refine (Metric.totallyBounded_iff).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hApprox ε hε with ⟨ψ, hψc, hψcs, hψ0, hψint, htrans⟩
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
  have hB_compact : IsCompact (closure B) :=
    smoothL2_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hB_tot : TotallyBounded B :=
    (totallyBounded_closure).1 hB_compact.totallyBounded
  rcases Metric.finite_approx_of_totallyBounded hB_tot (ε / 2) hε2 with ⟨t, htB, htfin, hBcover⟩
  refine ⟨t, htfin, ?_⟩
  intro x hx
  rcases hx with ⟨u, huA, rfl⟩
  have huR : u ∈ Metric.closedBall (0 : _) R := hA huA
  have hSu_mem : smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈ B := ⟨u, huR, rfl⟩
  have hSu_cover :
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈
        ⋃ y, ⋃ (_ : y ∈ t), Metric.ball y (ε / 2) :=
    hBcover hSu_mem
  rcases Set.mem_iUnion.1 hSu_cover with ⟨y, hy⟩
  rcases Set.mem_iUnion.1 hy with ⟨hyT, hyBall⟩
  have hyDist : dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y < ε / 2 := by
    simpa [Metric.ball, Set.mem_setOf_eq] using hyBall
  have hdist_smooth_ext :
      dist (extendByZeroL2 (E := E) (K := K) hKm u)
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) ≤ ε / 2 := by
    have hη : 0 ≤ ε / 2 := le_of_lt hε2
    have hnorm :
        ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ ε / 2 :=
      norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
        (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs hψ0 hψint (η := ε / 2) hη u (htrans u huA)
    -- Switch to `dist` with the argument order used by `dist_triangle`.
    have hdist :
        dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            (extendByZeroL2 (E := E) (K := K) hKm u) ≤ ε / 2 := by
      simpa [dist_eq_norm] using hnorm
    simpa [dist_comm] using hdist
  have hxDist : dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε := by
    have htri :=
      dist_triangle (extendByZeroL2 (E := E) (K := K) hKm u)
        (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
    have hlt :
        dist (extendByZeroL2 (E := E) (K := K) hKm u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            + dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
          < ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt hdist_smooth_ext hyDist
    have htmp :
        dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε / 2 + ε / 2 :=
      lt_of_le_of_lt htri hlt
    simpa [add_halves ε] using htmp
  have hxBall : extendByZeroL2 (E := E) (K := K) hKm u ∈ Metric.ball y ε := by
    simpa [Metric.ball, Set.mem_setOf_eq] using hxDist
  exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyT, hxBall⟩⟩

theorem isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    IsCompact (closure (extendByZeroL2 (E := E) (K := K) hKm '' A)) := by
  have ht :
      TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) :=
    totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) hK hKm hR hA hApprox
  exact (ht.closure).isCompact_of_isClosed isClosed_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1`

Extend Euclidean `L²` translation estimates from `C¹_c` to the closure-based Euclidean `H¹` space.

## Main results

- `norm_translateL2_sub_h1ToL2_le`: for `u ∈ H¹`, `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`, where `∇u` is the
  `L²(E)` component in our `H¹ ⊆ L² × L²(E)` model.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimateH1_r9eac31_1 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1_r9eac31_1 :
    OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanTranslationEstimateH1_r9eac31_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

/-- `H¹` translation estimate via closure: `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`. -/
theorem norm_translateL2_sub_h1ToL2_le (a : E) (u : ↥(h1 (μ := μ) (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (h1ToL2 (μ := μ) (E := E) u) -
        h1ToL2 (μ := μ) (E := E) u‖ ≤
      ‖a‖ * ‖h1ToL2Grad (μ := μ) (E := E) u‖ := by
  classical
  -- Work in the ambient space `L² × L²(E)`.
  let V : Type _ := (E →₂[μ] ℝ) × (E →₂[μ] E)
  let S : Set V :=
    {v |
      ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ ≤
        ‖a‖ * ‖v.2‖}
  have hS_closed : IsClosed S := by
    -- Closedness follows from continuity of both sides.
    have hf :
        Continuous fun v : V =>
          ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ := by
      -- `v ↦ v.1` is continuous, translation is continuous,
      -- subtraction is continuous, and norm is continuous.
      have hfst : Continuous fun v : V => v.1 := continuous_fst
      have htr :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 := by
        -- `translateL2` is a continuous linear isometry.
        exact (translateL2 (μ := μ) (F := ℝ) a).toContinuousLinearMap.continuous.comp hfst
      have hsub :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 - v.1 := by
        exact htr.sub hfst
      exact (continuous_norm.comp hsub)
    have hg :
        Continuous fun v : V =>
          ‖a‖ * ‖v.2‖ := by
      have hsnd : Continuous fun v : V => v.2 := continuous_snd
      have hnorm : Continuous fun v : V => ‖v.2‖ := continuous_norm.comp hsnd
      exact (continuous_const.mul hnorm)
    exact isClosed_le hf hg
  have hRange : (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S := by
    rintro v ⟨f, rfl⟩
    -- Reduce to the `C¹_c` estimate.
    simpa [S, graph, toL2Linear, toL2GradLinear] using
      norm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hClosure :
      closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S :=
    closure_minimal hRange hS_closed
  have hu :
      (u : V) ∈ closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) := by
    -- `u ∈ H¹` means `u` is in the topological closure of the range of `graph`.
    have hu0 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := by
      have hu0 : (u : V) ∈ h1 (μ := μ) (E := E) := u.2
      dsimp [h1] at hu0
      exact hu0
    have hu1 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := hu0
    rw [Submodule.topologicalClosure_coe] at hu1
    exact hu1
  have huS : (u : V) ∈ S := hClosure hu
  -- Unpack membership in `S` and rewrite in terms of the bundled maps `h1ToL2` and `h1ToL2Grad`.
  simpa [S, V, h1ToL2, h1ToL2Grad] using huS

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`

Euclidean Rellich–Kondrachov compactness for fixed compact support (Lebesgue `volume`).

This file discharges the “Euclidean heart” needed by the manifold Rellich glue:
for a fixed compact set `K ⊆ E`, the inclusion `H¹ → L²` is compact when restricted to the closed
subspace of `H¹` whose `L²` component is supported in `K` (a.e.).

The proof uses:

1. the Euclidean `H¹` translation estimate
   `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂` (`TranslationEstimateH1`);
2. the Fréchet–Kolmogorov / smoothing-based `L²` compactness criterion
   (`L2CompactnessCriterion`).

## Main definitions / results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On`:
  the closed subspace of `H¹(volume)` whose `L²` component is supported in `K` (a.e.).
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2`:
  the restricted inclusion map `h1On K →L[ℝ] L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2`:
  compactness of the inclusion.

Tracking: Beads `lean-103.5.2.26.5.3.2.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-! ### Supported `H¹` subspace -/

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceE_SobolevEuclideanRellich
local instance instOpensMeasurableSpaceE_SobolevEuclideanRellich_r9eac31_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableAddE_SobolevEuclideanRellich_r9eac31_1 : MeasurableAdd E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
local instance instMeasurableNegE_SobolevEuclideanRellich_r9eac31_1 : MeasurableNeg E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instFactOneLeTwo_SobolevEuclideanRellich
/-- The subspace of `H¹(volume)` whose `L²` component is (a.e.) supported in `K`.

We model “supported in `K`” as belonging to the closed range of the extension-by-zero map
`Lp(volume.restrict K) →ₗᵢ Lp(volume)`. -/
noncomputable def h1On (K : Set E) (hKm : MeasurableSet K) :
    Submodule ℝ (↥(h1 (μ := (volume : Measure E)) (E := E))) :=
  Submodule.comap
    (h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
    (LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))

/-- The inclusion `h1On K → L²(volume)` as a continuous linear map. -/
noncomputable def h1OnToL2 (K : Set E) (hKm : MeasurableSet K) :
    ↥(h1On K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
  (h1ToL2 (μ := (volume : Measure E)) (E := E)).comp (h1On K hKm).subtypeL

/-! ### Euclidean Rellich on fixed compact support -/

set_option maxHeartbeats 2000000 in
/-- Euclidean Rellich–Kondrachov compactness (Lebesgue): on a fixed compact support `K`, the
inclusion `H¹ → L²` is a compact operator. -/
theorem isCompactOperator_h1OnToL2 {K : Set E} (_hK : IsCompact K) (hKm : MeasurableSet K) :
    IsCompactOperator (h1OnToL2 (E := E) K hKm) := by
  classical
  have hr : (0 : ℝ) < 1 := by norm_num
  let H1vol : Type _ := ↥(h1 (μ := (volume : Measure E)) (E := E))
  let T : ↥(h1On (E := E) K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
    h1OnToL2 (E := E) K hKm
  let A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K)) :=
    {u |
      L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u ∈
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1}
  let C : ℝ :=
    (h1ToL2 (μ := (volume : Measure E)) (E := E)).opNorm
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact (h1ToL2 (μ := (volume : Measure E)) (E := E)).opNorm_nonneg
  have hA_ball :
      A ⊆
        Metric.closedBall
          (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K))
          C := by
    intro u hu
    rcases hu with ⟨x, hx, hxEq⟩
    have hx' : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      -- `h1On` inherits the ambient norm, so this is definitional.
      change ‖x‖ ≤ (1 : ℝ)
      have hd := Metric.mem_closedBall.mp hx
      rw [Subtype.dist_eq] at hd
      simpa [dist_eq_norm] using hd
    have hTx' : ‖T x‖ ≤ C := by
      have hTx : ‖T x‖ ≤ C * ‖(x : H1vol)‖ := by
        have h :=
          (h1ToL2 (μ := (volume : Measure E)) (E := E)).le_opNorm (x : H1vol)
        first | exact h | simpa [T, h1OnToL2, C] using h
      refine hTx.trans ?_
      have : C * ‖(x : H1vol)‖ ≤ C * (1 : ℝ) := mul_le_mul_of_nonneg_left hx' hCnonneg
      simpa [mul_one] using this
    have hnorm_ext :
        ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ :=
      L2Compactness.norm_extendByZeroL2 (E := E) (K := K) hKm u
    have hu' : ‖u‖ ≤ C := by
      have : ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ C := by
        simpa [hxEq] using hTx'
      simpa [hnorm_ext] using this
    simpa [Metric.closedBall, dist_eq_norm] using hu'
  have hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u)
                    - L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂L2Compactness.kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2 := by
    intro ε hε
    have hδ : 0 < ε / 2 := by linarith
    rcases
        L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one
          (E := E) (δ := ε / 2) hδ with
      ⟨ψ, hψc, hψcs, hψ0, hψint, hψsupp⟩
    refine ⟨ψ, hψc, hψcs, hψ0, hψint, ?_⟩
    intro u huA
    rcases huA with ⟨x, hx, hxEq⟩
    have hxH1 : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      change ‖x‖ ≤ (1 : ℝ)
      have hd := Metric.mem_closedBall.mp hx
      rw [Subtype.dist_eq] at hd
      simpa [dist_eq_norm] using hd
    have hmod :
        ∀ t : E, t ∈ Metric.ball (0 : E) (ε / 2) →
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤ ε / 2 := by
      intro t ht
      have ht' : ‖t‖ ≤ ε / 2 := le_of_lt (by
        simpa [Metric.ball, dist_eq_norm, mem_setOf_eq] using ht)
      have hgrad_le :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ ‖(x : H1vol)‖ := by
        let V : Type _ := (E →₂[(volume : Measure E)] ℝ) × (E →₂[(volume : Measure E)] E)
        simpa [h1ToL2Grad, V] using (norm_snd_le (x := ((x : H1vol) : V)))
      have hgrad_le_one :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (1 : ℝ) :=
        hgrad_le.trans hxH1
      have htr :=
        norm_translateL2_sub_h1ToL2_le (μ := (volume : Measure E)) (E := E) (-t) (x : H1vol)
      have htr' :
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol))
              - h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [neg_neg] using htr
      have hle :
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [T, h1OnToL2, hxEq] using htr'
      refine hle.trans ?_
      have :
          ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (ε / 2) * 1 := by
        refine (mul_le_mul_of_nonneg_right ht' (norm_nonneg _)).trans ?_
        refine mul_le_mul_of_nonneg_left hgrad_le_one (by linarith)
      simpa [mul_one] using this
    have hη : 0 ≤ ε / 2 := le_of_lt hδ
    have hbound :=
      L2Compactness.integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
        (E := E) (ψ := ψ) hψc hψcs hψ0 hψint (δ := ε / 2) (η := ε / 2) hη hψsupp (T x) hmod
    simpa [hxEq] using hbound
  have hcomp : IsCompact (closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1)) := by
    have hR : 0 ≤ C := hCnonneg
    have hA_eq :
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1 =
          L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxRange :
            (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)) ∈
              LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := (volume : Measure E)) (E := ℝ)
                      (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
          -- Unfold membership in the defining `comap` without
          -- letting `simp` use `x.property`
          -- (which would rewrite the goal to `True`).
          have hxmem :
              (x : H1vol) ∈ h1On (E := E) K hKm := x.property
          dsimp [h1On] at hxmem
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : H1vol)) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          exact hxmem
        rcases hxRange with ⟨u, hu⟩
        have hu0 :
            (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u =
              h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
          simpa using hu
        have hTx : T x = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
          calc
            T x = h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
                  simp [T, h1OnToL2]
            _ = (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u := by
                  simpa using hu0.symm
            _ = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
                  simpa using
                    (L2Compactness.extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u).symm
        refine ⟨u, ?_, hTx.symm⟩
        exact ⟨x, hx, hTx⟩
      · intro hy
        rcases hy with ⟨u, huA, rfl⟩
        exact huA
    have : IsCompact
        (closure (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A)) :=
    L2Compactness.isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) (hK := (_hK : IsCompact K))
      (hKm := hKm) hR hA_ball hApprox
    simpa [hA_eq] using this
  -- Use the topological definition of `IsCompactOperator` to avoid expensive normed-space
  -- characterizations.
  refine ⟨closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1), hcomp, ?_⟩
  have hball :
      Metric.ball (0 : ↥(h1On (E := E) K hKm)) 1 ⊆
        T ⁻¹' closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1) := by
    intro x hx
    refine subset_closure ?_
    refine ⟨x, ?_, rfl⟩
    exact Metric.ball_subset_closedBall hx
  exact Filter.mem_of_superset
    (Metric.ball_mem_nhds (x := (0 : ↥(h1On (E := E) K hKm))) (ε := (1 : ℝ)) hr) hball

/-!
### Codomain restriction and a compact map into `L²(volume.restrict K)`

The definition of `h1On` forces the image of `h1OnToL2` to lie in the (closed) range of the
extension-by-zero map from `volume.restrict K`. We record a codomain-restricted version and a
convenient compact map to the restricted `L²` space.
-/

omit [CompleteSpace E] in
lemma isClosed_range_extendByZero (K : Set E) (hKm : MeasurableSet K) :
    IsClosed
      (LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) :
        Set (E →₂[(volume : Measure E)] ℝ)) := by
  classical
  let e :=
    MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm
  have hcr : IsClosed (Set.range (fun u => e u)) :=
    (e.isometry.isClosedEmbedding).isClosed_range
  have hEq :
      (Set.range (fun u => e u)) =
        (LinearMap.range e.toLinearMap : Set (E →₂[(volume : Measure E)] ℝ)) := by
    ext y
    constructor <;> rintro ⟨u, rfl⟩ <;> exact ⟨u, rfl⟩
  simpa [hEq] using hcr

end Volume

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.Analysis_FunctionalSpaces_Sobolev_Euclidean_SupportedH1
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.SupportedH1`

Supported Euclidean `H¹` subspaces for a general measure.

This file defines the `H¹` subspace of functions whose `L²` component is (a.e.) supported in a
measurable set `K`, modeled as membership in the closed range of the extension-by-zero map
`Lp (μ.restrict K) →ₗᵢ Lp μ`.

These definitions match the volume-specialized `h1On` construction used by
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`, but are stated for an
arbitrary measure `μ`. Compactness results are proven elsewhere.

## Main definitions

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure`
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2Measure`
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [CompleteSpace E]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanSupportedH1
local instance instBorelSpaceE_SobolevEuclideanSupportedH1_r9eac31_1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanSupportedH1_r9eac31_1 : OpensMeasurableSpace E := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {K : Set E} (hKm : MeasurableSet K)

/-! ## Range characterization for extension-by-zero -/

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instFactOneLeTwo_SobolevEuclideanSupportedH1
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [IsFiniteMeasureOnCompacts μ] in
/-- If a function is supported in `K`, then its `Lp` class belongs to the range of `extendByZeroₗᵢ`
from the restricted measure `μ.restrict K`. -/
lemma mem_range_extendByZeroₗᵢ_toLp_of_tsupport_subset {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) μ) (hK : tsupport f ⊆ K) :
    (hf.toLp f) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μ) (E := F) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
  classical
  -- Define the restricted `Lp` class and show its extension by zero matches `hf.toLp f`.
  have hfK : MeasureTheory.MemLp f (2 : ℝ≥0∞) (μ.restrict K) := hf.restrict K
  let u : MeasureTheory.Lp F (2 : ℝ≥0∞) (μ.restrict K) := hfK.toLp f
  refine ⟨u, ?_⟩
  refine MeasureTheory.Lp.ext (μ := μ) (E := F) (p := (2 : ℝ≥0∞)) ?_
  have hu_ae_restrict : (u : E → F) =ᵐ[μ.restrict K] f :=
    (MeasureTheory.MemLp.coeFn_toLp (μ := μ.restrict K) (p := (2 : ℝ≥0∞)) (f := f) hfK)
  have hu_ae_on :
      ∀ᵐ x ∂μ, x ∈ K → (u : E → F) x = f x := by
    exact (ae_restrict_iff' (μ := μ) (s := K) hKm).1 hu_ae_restrict
  have hExt_ae :
      (((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μ) (E := F) (p := (2 : ℝ≥0∞))
              (s := K) hKm) u :
            MeasureTheory.Lp F (2 : ℝ≥0∞) μ) :
            E → F) =ᵐ[μ] K.indicator fun x : E => (u : E → F) x := by
    simpa using
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := μ) (E := F) (p := (2 : ℝ≥0∞)) (s := K) hKm u)
  have hf_ae : ((hf.toLp f : MeasureTheory.Lp F (2 : ℝ≥0∞) μ) : E → F) =ᵐ[μ] f :=
    (MeasureTheory.MemLp.coeFn_toLp (μ := μ) (p := (2 : ℝ≥0∞)) (f := f) hf)
  -- Combine: on `K` use `hu_ae_on`; off `K` use pointwise support control.
  filter_upwards [hExt_ae, hf_ae, hu_ae_on] with x hxExt hxLp hxOn
  by_cases hxK : x ∈ K
  · -- on `K`, the indicator is `u`, and `u = f`.
    calc
      ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μ) (E := F) (p := (2 : ℝ≥0∞)) (s := K) hKm) u : E → F) x =
          (K.indicator (fun y : E => (u : E → F) y)) x := hxExt
      _ = (u : E → F) x := by simp [hxK]
      _ = f x := hxOn hxK
      _ = (hf.toLp f : E → F) x := by simpa using hxLp.symm
  · -- off `K`, the indicator is `0`, and `f x = 0`.
    have hfx : f x = 0 := by
      have : x ∉ tsupport f := by
        exact fun hx' => hxK (hK hx')
      simpa using (image_eq_zero_of_notMem_tsupport (f := f) this)
    simp [hxK, hxExt, hxLp, hfx]

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Orientation distinguishes the two explicit quaternionic two-form spaces. -/

namespace PositiveEinsteinFour.QuaternionFrame

open Matrix TraceHessian PositiveEinsteinFour.Geometry
open Angular (oppositeMatrix)
open scoped BigOperators

noncomputable section

/-- The Pfaffian with respect to the fixed orientation of four coordinates. -/
def pfaffianFour (A : Mat4) : ℝ :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

def upperSquareFour (A : Mat4) : ℝ :=
  A 0 1 ^ 2 + A 0 2 ^ 2 + A 0 3 ^ 2 +
    A 1 2 ^ 2 + A 1 3 ^ 2 + A 2 3 ^ 2

theorem sandwich_apply (P A : Mat4) (i j : Fin 4) :
    (P * A * Pᵀ) i j = ∑ a, ∑ b, P i a * A a b * P j b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem pfaffian_opposite_zero (P : Mat4) :
    pfaffianFour (P * oppositeMatrix 0 * Pᵀ) = -P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  simp [oppositeMatrix, oppositeQuaternion, quaternionMatrix,
    Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

theorem pfaffian_opposite_one (P : Mat4) :
    pfaffianFour (P * oppositeMatrix 1 * Pᵀ) = -P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  simp [oppositeMatrix, oppositeQuaternion, quaternionMatrix,
    Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

theorem pfaffian_opposite_two (P : Mat4) :
    pfaffianFour (P * oppositeMatrix 2 * Pᵀ) = -P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  simp [oppositeMatrix, oppositeQuaternion, quaternionMatrix,
    Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

theorem pfaffian_opposite (P : Mat4) (s : Fin 3) :
    pfaffianFour (P * oppositeMatrix s * Pᵀ) = -P.det := by
  fin_cases s
  · exact pfaffian_opposite_zero P
  · exact pfaffian_opposite_one P
  · exact pfaffian_opposite_two P

theorem skew_diagonal_zero (A : Mat4)
    (hsk : ∀ i j, A i j = -A j i) (i : Fin 4) : A i i = 0 := by
  linarith [hsk i i]

theorem upperSquareFour_eq_two (A : Mat4)
    (hsk : ∀ i j, A i j = -A j i) (hA : Aᵀ * A = 1) :
    upperSquareFour A = 2 := by
  have hd (i : Fin 4) : ∑ k, A k i ^ 2 = 1 := by
    have h := congrArg (fun B : Mat4 => B i i) hA
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  simp only [Fin.sum_univ_four, skew_diagonal_zero A hsk,
    hsk 1 0, hsk 2 0, hsk 3 0, hsk 2 1, hsk 3 1, hsk 3 2,
    neg_sq, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, add_zero] at h0 h1 h2 h3
  dsimp [upperSquareFour]
  linarith

theorem antiSelfDual_of_pfaffian (A : Mat4)
    (hupper : upperSquareFour A = 2) (hpf : pfaffianFour A = -1) :
    A 2 3 = -A 0 1 ∧ A 1 3 = A 0 2 ∧ A 1 2 = -A 0 3 := by
  have hsq : (A 0 1 + A 2 3) ^ 2 + (A 0 2 - A 1 3) ^ 2 +
      (A 0 3 + A 1 2) ^ 2 = 0 := by
    dsimp [upperSquareFour] at hupper
    dsimp [pfaffianFour] at hpf
    nlinarith
  have h1 : (A 0 1 + A 2 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 2 - A 1 3), sq_nonneg (A 0 3 + A 1 2)]
  have h2 : (A 0 2 - A 1 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 1 + A 2 3), sq_nonneg (A 0 3 + A 1 2)]
  have h3 : (A 0 3 + A 1 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 1 + A 2 3), sq_nonneg (A 0 2 - A 1 3)]
  have := sq_eq_zero_iff.mp h1
  have := sq_eq_zero_iff.mp h2
  have := sq_eq_zero_iff.mp h3
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem antiSelfDual_span (A : Mat4)
    (hsk : ∀ i j, A i j = -A j i)
    (hp : A 2 3 = -A 0 1 ∧ A 1 3 = A 0 2 ∧ A 1 2 = -A 0 3) :
    A = imaginaryCombination oppositeMatrix (fun r => -A r.succ 0) := by
  have hd := skew_diagonal_zero A hsk
  ext i j
  simp only [imaginaryCombination_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [oppositeMatrix, oppositeQuaternion, quaternionMatrix]
  all_goals first | exact hd _ | linarith [hsk 0 1, hsk 0 2, hsk 0 3, hsk 1 2, hsk 1 3, hsk 2 3, hp.1, hp.2.1, hp.2.2]

theorem conjugate_orthogonal (P A : Mat4)
    (hP : Pᵀ * P = 1) (hA : Aᵀ * A = 1) :
    (P * A * Pᵀ)ᵀ * (P * A * Pᵀ) = 1 := by
  have hPP : P * Pᵀ = 1 := mul_eq_one_comm.mp hP
  calc
    _ = P * Aᵀ * (Pᵀ * P) * A * Pᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = P * (Aᵀ * A) * Pᵀ := by rw [hP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hPP]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The finite curvature contractions occurring in the four-dimensional
Euler and first Pontryagin densities.  These are pointwise identities for
the actual metric curvature; no characteristic-number or Hodge theorem is
assumed or asserted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

/-- Hodge star on two-forms in the positively oriented standard basis.
The input is represented by a skew matrix; the formula also defines a
linear map on arbitrary matrices. -/
def hodgeStarFour : Mat4 →ₗ[ℝ] Mat4 where
  toFun A := !![0, A 2 3, -A 1 3, A 1 2;
    -A 2 3, 0, A 0 3, -A 0 2;
    A 1 3, -A 0 3, 0, A 0 1;
    -A 1 2, A 0 2, -A 0 1, 0]
  map_add' A B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' r A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem hodgeStarFour_quaternion (s : Fin 3) :
    hodgeStarFour (quaternionMatrix s) = quaternionMatrix s := by
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;> norm_num [hodgeStarFour, quaternionMatrix]

theorem hodgeStarFour_opposite (s : Fin 3) :
    hodgeStarFour (oppositeMatrix s) = -oppositeMatrix s := by
  ext i j
  change hodgeStarFour (oppositeMatrix s) i j = -(oppositeMatrix s i j)
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [hodgeStarFour, oppositeMatrix, oppositeQuaternion, quaternionMatrix]

/-- The curvature polynomial whose integral is the Euler number in the
Chern--Gauss--Bonnet theorem.  That global theorem is not used here. -/
def curvatureEulerDensity (R : CovariantCoordinates 4) : ℝ :=
  (frameTensorSquareNorm R -
    4 * ∑ j, ∑ k, (∑ i : Fin 4, R ![i, j, k, i]) ^ 2 +
    (∑ j, ∑ i : Fin 4, R ![i, j, j, i]) ^ 2) / (32 * Real.pi ^ 2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two-form Hodge operator is independent of the chosen positively
oriented orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian QuaternionFrame Angular
open scoped BigOperators

noncomputable section

theorem hodgeStarFour_quaternion_combination (u : Fin 3 → ℝ) :
    hodgeStarFour (imaginaryCombination quaternionMatrix u) =
      imaginaryCombination quaternionMatrix u := by
  simp only [imaginaryCombination, map_sum, map_smul, hodgeStarFour_quaternion]

theorem hodgeStarFour_opposite_combination (u : Fin 3 → ℝ) :
    hodgeStarFour (imaginaryCombination oppositeMatrix u) =
      -imaginaryCombination oppositeMatrix u := by
  simp only [imaginaryCombination, map_sum, map_smul, hodgeStarFour_opposite,
    smul_neg, Finset.sum_neg_distrib]

theorem sandwich_combination (P : Mat4) (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ) :
    P * imaginaryCombination Q u * Pᵀ = imaginaryCombination (fun s => P * Q s * Pᵀ) u := by
  simp only [imaginaryCombination, Matrix.mul_sum, Matrix.sum_mul,
    mul_smul_comm, smul_mul_assoc]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_EuclideanHausdorffFactor
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Euclidean four-dimensional Hausdorff measure is a fixed positive
multiple of Lebesgue measure. Its numerical normalization is immaterial
for the normalized canonical frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped ENNReal NNReal

noncomputable section

local instance instIsAddHaarMeasureFourSpaceHausdorffMeasureOfNatReal : Measure.IsAddHaarMeasure
    (Measure.hausdorffMeasure 4 : Measure FourSpace) := by
  simpa [FourSpace] using
    (inferInstance : Measure.IsAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ FourSpace) : Measure FourSpace))

def euclideanHausdorffFactor : ℝ≥0 :=
  (Measure.hausdorffMeasure 4 : Measure FourSpace).addHaarScalarFactor volume

theorem euclideanHausdorffFactor_pos : 0 < euclideanHausdorffFactor :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem euclideanHausdorff_eq_smul_volume :
    (Measure.hausdorffMeasure 4 : Measure FourSpace) = euclideanHausdorffFactor • volume :=
  Measure.isAddLeftInvariant_eq_smul _ _

theorem euclideanHausdorff_apply (s : Set FourSpace) :
    (Measure.hausdorffMeasure 4 : Measure FourSpace) s =
      (euclideanHausdorffFactor : ℝ≥0∞) * volume s := by
  rw [euclideanHausdorff_eq_smul_volume, Measure.smul_apply]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.vector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized Euclidean four-dimensional Gaussian used in the local
heat construction. All integrals use the actual Euclidean volume measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory GaussianFourier

noncomputable section

theorem fourHeatGaussian_pos (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    0 < fourHeatGaussian t x := by
  unfold fourHeatGaussian
  positivity

theorem fourHeatGaussian_integrable (t : ℝ) (ht : 0 < t) : Integrable (fourHeatGaussian t) :=
  (fourGaussian_integrable (4 * t)⁻¹ (by positivity)).const_mul _

theorem fourHeatGaussian_mass (t : ℝ) (ht : 0 < t) :
    (∫ x : FourSpace, fourHeatGaussian t x) = 1 := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  have hg := integral_rexp_neg_mul_sq_norm (V := FourSpace) hb
  have hd : Module.finrank ℝ FourSpace = 4 := by simp [FourSpace]
  have hd2 : (Module.finrank ℝ FourSpace : ℝ) / 2 = 2 := by norm_num [hd]
  rw [hd2, Real.rpow_two] at hg
  simp only [fourHeatGaussian]
  rw [integral_const_mul, hg]
  have ht0 := ne_of_gt ht
  field_simp [Real.pi_ne_zero, ht0]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianApproximation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.vector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian dilation and its actual approximate-identity limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped _root_.Topology

noncomputable section

theorem fourHeatGaussian_dilate (t : ℝ) (ht : 0 < t) (z : FourSpace) :
    t ^ 2 * fourHeatGaussian t (Real.sqrt t • z) = fourHeatGaussian 1 z := by
  have hs : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have he : -(4 * t)⁻¹ * ‖Real.sqrt t • z‖ ^ 2 = -(4 : ℝ)⁻¹ * ‖z‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs]
    field_simp
  unfold fourHeatGaussian
  rw [he]
  norm_num only [mul_one]
  field_simp [Real.pi_ne_zero]

theorem fourHeatGaussian_integral_dilate (t : ℝ) (ht : 0 < t)
    (f : FourSpace → ℝ) (x : FourSpace) :
    (∫ z : FourSpace, fourHeatGaussian t z * f (x - z)) =
      ∫ z : FourSpace, fourHeatGaussian 1 z * f (x - Real.sqrt t • z) := by
  have hs : (Real.sqrt t) ^ 4 = t ^ 2 := by
    calc
      (Real.sqrt t) ^ 4 = ((Real.sqrt t) ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [Real.sq_sqrt ht.le]
  have h := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure FourSpace))
    (fun z => fourHeatGaussian t z * f (x - z)) (Real.sqrt t)
      (hR := Real.sqrt_nonneg _)
  have hdim : Module.finrank ℝ FourSpace = 4 := by simp [FourSpace]
  rw [hdim, hs, smul_eq_mul] at h
  have he (z : FourSpace) : fourHeatGaussian t (Real.sqrt t • z) *
      f (x - Real.sqrt t • z) = (t ^ 2)⁻¹ *
        (fourHeatGaussian 1 z * f (x - Real.sqrt t • z)) := by
    have hk := fourHeatGaussian_dilate t ht z
    have hk' : fourHeatGaussian t (Real.sqrt t • z) = (t ^ 2)⁻¹ * fourHeatGaussian 1 z := by
      calc
        _ = (t ^ 2)⁻¹ * (t ^ 2 * fourHeatGaussian t (Real.sqrt t • z)) := by
          field_simp
        _ = _ := by rw [hk]
    rw [hk']
    ring
  simp_rw [he] at h
  rw [integral_const_mul] at h
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 ht.ne')) h.symm

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianConvolution
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.vector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Completing the square gives the exact Euclidean heat semigroup. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

theorem fourHeatGaussian_product (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (x y : FourSpace) :
    fourHeatGaussian t (x - y) * fourHeatGaussian s y =
      fourHeatGaussian (t + s) x *
        fourHeatGaussian (t * s / (t + s)) (y - (s / (t + s)) • x) := by
  have hts : t + s ≠ 0 := ne_of_gt (add_pos ht hs)
  have hp : (((4 * Real.pi * t) ^ 2)⁻¹ * ((4 * Real.pi * s) ^ 2)⁻¹) =
      ((4 * Real.pi * (t + s)) ^ 2)⁻¹ *
        ((4 * Real.pi * (t * s / (t + s))) ^ 2)⁻¹ := by
    field_simp [Real.pi_ne_zero]
  unfold fourHeatGaussian
  calc
    _ = (((4 * Real.pi * t) ^ 2)⁻¹ * ((4 * Real.pi * s) ^ 2)⁻¹) *
        Real.exp (-(4 * t)⁻¹ * ‖x - y‖ ^ 2 + -(4 * s)⁻¹ * ‖y‖ ^ 2) := by
      rw [Real.exp_add]
      ring
    _ = _ := by
      rw [hp, fourHeatGaussian_complete_square t s ht hs x y, Real.exp_add]
      ring

theorem fourHeatGaussian_convolution (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (x : FourSpace) :
    (∫ y : FourSpace, fourHeatGaussian t (x - y) * fourHeatGaussian s y) =
      fourHeatGaussian (t + s) x := by
  simp_rw [fourHeatGaussian_product t s ht hs x]
  rw [integral_const_mul, integral_sub_right_eq_self,
    fourHeatGaussian_mass (t * s / (t + s)) (div_pos (mul_pos ht hs) (add_pos ht hs)),
    mul_one]

theorem fourHeatGaussian_product_integrable (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (x : FourSpace) :
    Integrable (fun y : FourSpace => fourHeatGaussian t (x - y) * fourHeatGaussian s y) := by
  simp_rw [fourHeatGaussian_product t s ht hs x]
  exact ((fourHeatGaussian_integrable (t * s / (t + s))
    (div_pos (mul_pos ht hs) (add_pos ht hs))).comp_sub_right _).const_mul _

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.vector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial absorption and actual Gaussian moment bounds for the local
heat remainder. These bounds use Euclidean volume and the proved unit mass. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

theorem fourHeatGaussian_half_exponent (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    fourHeatGaussian t x =
      4 * Real.exp (-(8 * t)⁻¹ * ‖x‖ ^ 2) * fourHeatGaussian (2 * t) x := by
  have h8 : 4 * (2 * t) = 8 * t := by ring
  have he : -(4 * t)⁻¹ * ‖x‖ ^ 2 =
      -(8 * t)⁻¹ * ‖x‖ ^ 2 + -(8 * t)⁻¹ * ‖x‖ ^ 2 := by
    field_simp
    ring
  unfold fourHeatGaussian
  rw [h8, he, Real.exp_add]
  field_simp [Real.pi_ne_zero]
  ring

theorem fourHeatGaussian_moment_bound (m : ℕ) (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    ‖x‖ ^ (2 * m) * fourHeatGaussian t x ≤
      (4 * (m.factorial : ℝ) * (8 * t) ^ m) * fourHeatGaussian (2 * t) x := by
  let z := ‖x‖ ^ 2 / (8 * t)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have he : -(8 * t)⁻¹ * ‖x‖ ^ 2 = -z := by dsimp [z]; ring
  have hp : ‖x‖ ^ (2 * m) = (8 * t) ^ m * z ^ m := by
    dsimp [z]
    rw [div_pow, ← pow_mul]
    field_simp
  rw [fourHeatGaussian_half_exponent t ht, he, hp]
  have h := mul_le_mul_of_nonneg_left (fourHeatPolynomial_absorption m z hz)
    (show 0 ≤ 4 * (8 * t) ^ m * fourHeatGaussian (2 * t) x by
      exact mul_nonneg (by positivity) (fourHeatGaussian_pos _ (by positivity) x).le)
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

theorem fourHeatGaussian_moment_integrable (m : ℕ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : FourSpace => ‖x‖ ^ (2 * m) * fourHeatGaussian t x) := by
  have hmajor := (fourHeatGaussian_integrable (2 * t) (by positivity)).const_mul
    (4 * (m.factorial : ℝ) * (8 * t) ^ m)
  have hm : AEStronglyMeasurable
      (fun x : FourSpace => ‖x‖ ^ (2 * m) * fourHeatGaussian t x) volume :=
    ((continuous_norm.pow _).mul (fourHeatGaussian_continuous t)).aestronglyMeasurable
  exact hmajor.mono_nonneg hm
    (Filter.Eventually.of_forall fun x =>
      mul_nonneg (by positivity) (fourHeatGaussian_pos t ht x).le)
    (Filter.Eventually.of_forall (fourHeatGaussian_moment_bound m t ht))

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianSquare
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.vector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L2 mass of the four-dimensional heat Gaussian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

theorem fourHeatGaussian_square_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : FourSpace => fourHeatGaussian t x ^ 2) := by
  have h := fourHeatGaussian_product_integrable t t ht ht 0
  simpa only [fourHeatGaussian, zero_sub, norm_neg, pow_two] using h

theorem fourHeatGaussian_square_mass (t : ℝ) (ht : 0 < t) :
    (∫ x : FourSpace, fourHeatGaussian t x ^ 2) = 1 / (64 * Real.pi ^ 2 * t ^ 2) := by
  have h := fourHeatGaussian_convolution t t ht ht 0
  have he : (fun x : FourSpace => fourHeatGaussian t (0 - x) * fourHeatGaussian t x) =
      (fun x => fourHeatGaussian t x ^ 2) := by
    funext x
    simp only [fourHeatGaussian, zero_sub, norm_neg, pow_two]
  rw [he] at h
  rw [h, fourHeatGaussian]
  simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.exp_zero, mul_one]
  field_simp
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianTimeRegularity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.vector_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint positive-time continuity of the Gaussian and its actual time derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped _root_.Topology

noncomputable section

theorem fourHeatGaussian_joint_continuousOn :
    ContinuousOn (fun z : ℝ × FourSpace => fourHeatGaussian z.1 z.2) (Ioi 0 ×ˢ univ) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have ht : z.1 ≠ 0 := hz.1.ne'
  have hP : ContinuousAt (fun w : ℝ × FourSpace => ((4 * Real.pi * w.1) ^ 2)⁻¹) z :=
    ((continuousAt_const.mul continuousAt_fst).pow 2).inv₀
      (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht))
  have hE : ContinuousAt (fun w : ℝ × FourSpace => -(4 * w.1)⁻¹ * ‖w.2‖ ^ 2) z :=
    (((continuousAt_const.mul continuousAt_fst).inv₀ (mul_ne_zero (by norm_num) ht)).neg).mul
      (continuousAt_snd.norm.pow 2)
  exact hP.mul (Real.continuous_exp.continuousAt.comp hE)

theorem fourHeatGaussianTimeFactor_joint_continuousOn :
    ContinuousOn (fun z : ℝ × FourSpace => fourHeatGaussianTimeFactor z.1 z.2)
      (Ioi 0 ×ˢ univ) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have ht : z.1 ≠ 0 := hz.1.ne'
  exact ((continuousAt_snd.norm.pow 2).div
    (continuousAt_const.mul (continuousAt_fst.pow 2))
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))).sub
    (continuousAt_const.div continuousAt_fst ht)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RiemannianVolumeFinite
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness and bounded inverse-chart differentials imply finiteness
of the actual four-dimensional Riemannian Hausdorff measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem fourSpace_hausdorff_haar :
    Measure.IsAddHaarMeasure (Measure.hausdorffMeasure 4 : Measure FourSpace) := by
  simpa [FourSpace] using
    (inferInstance : Measure.IsAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ FourSpace) : Measure FourSpace))

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricQuadraticPerturbation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A four-dimensional entrywise perturbation estimate for the metric.
It converts continuity of the chart metric into almost-isometric norm
bounds after freezing an orthonormal frame at one point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem sum_abs_sq_le_four_norm_sq (v : FourSpace) :
    (∑ i : Fin 4, |v i|) ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4))
    (fun _ => (1 : ℝ)) (fun i => |v i|)
  simpa [EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs] using h

/-- The factor four is exactly the dimension, so an entrywise bound
of `δ/4` controls the complete quadratic form by `δ`. -/
theorem quadraticForm_entry_bound (A : Mat4) (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ i j, |A i j| ≤ δ / 4) (v : FourSpace) :
    |WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v)| ≤ δ * ‖v‖ ^ 2 := by
  have hsum : |∑ i : Fin 4, ∑ j : Fin 4, v i * A i j * v j| ≤
      (δ / 4) * (∑ i : Fin 4, |v i|) ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 4, |∑ j : Fin 4, v i * A i j * v j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, |v i * A i j * v j| := by
        exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, |v i| * (δ / 4) * |v j| := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hA i j) (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  calc
    _ = |∑ i : Fin 4, ∑ j : Fin 4, v i * A i j * v j| := by
      apply congrArg abs
      simp only [dotProduct, mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (δ / 4) * (∑ i : Fin 4, |v i|) ^ 2 := hsum
    _ ≤ (δ / 4) * (4 * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_abs_sq_le_four_norm_sq v) (by positivity)
    _ = δ * ‖v‖ ^ 2 := by ring

theorem quadraticForm_near_identity (A : Mat4) (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ i j, |A i j - (1 : Mat4) i j| ≤ δ / 4) (v : FourSpace) :
    (1 - δ) * ‖v‖ ^ 2 ≤ WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v) ∧
      WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v) ≤ (1 + δ) * ‖v‖ ^ 2 := by
  have h := quadraticForm_entry_bound (A - 1) δ hδ hA v
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec] at h
  have hnorm : WithLp.ofLp v ⬝ᵥ WithLp.ofLp v = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  rw [hnorm] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> nlinarith

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Ordinary derivatives of a coordinate geodesic variation give its
covariant Jacobi equation, with the actual Christoffel curvature sign. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem hasDerivAt_jacobi_mulVec (U : ℝ → Mat4)
    (y : ℝ → JacobiCoordinateVector) (U' : Mat4) (y' : JacobiCoordinateVector) (t : ℝ)
    (hU : ∀ i j, HasDerivAt (fun s => U s i j) (U' i j) t)
    (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => U s *ᵥ y s) (U' *ᵥ y t + U t *ᵥ y') t := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
    (hU i j).mul (hasDerivAt_pi.mp hy j))
  simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.mul_apply,
    Finset.sum_add_distrib] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature term in the coordinate Jacobi equation, expressed in
an actual orthonormal frame, has normal matrix `1 + frameCurvatureField`. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

/-- Multiplication by a parallel frame converts ordinary component
derivatives into covariant derivatives along the curve. -/
theorem hasDerivAt_parallel_frameVector (E : ℝ → Mat4)
    (y : ℝ → JacobiCoordinateVector) (U : Mat4) (y' : JacobiCoordinateVector)
    (t : ℝ) (hE : ∀ i j, HasDerivAt (fun s => E s i j) (-(U * E t) i j) t)
    (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => E s *ᵥ y s)
      (E t *ᵥ y' - U *ᵥ (E t *ᵥ y t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
    (hE i j).mul (hasDerivAt_pi.mp hy j))
  have heq : (∑ j, (-(U * E t) i j * y t j + E t i j * y' j)) =
      (E t *ᵥ y' - U *ᵥ (E t *ᵥ y t)) i := by
    rw [Matrix.mulVec_mulVec]
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct,
      neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  rw [heq] at h
  simpa only [Pi.mul_apply, Matrix.mulVec, dotProduct] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse parallel-frame coordinates of a variation and its covariant
derivative. The component equations follow by differentiating the inverse matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem jacobi_det_differentiableAt (E : ℝ → Mat4) (t : ℝ)
    (hE : ∀ i j, DifferentiableAt ℝ (fun s => E s i j) t) :
    DifferentiableAt ℝ (fun s => (E s).det) t := by
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  have hprod (s : Finset (Fin 4)) :
      DifferentiableAt ℝ (fun u => ∏ i ∈ s, E u (σ i) i) t := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using! (differentiableAt_const (1 : ℝ))
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi, Pi.mul_apply] using! (hE (σ i) i).mul ih
  exact (hprod Finset.univ).const_mul _

theorem jacobi_inverse_differentiableAt (E : ℝ → Mat4) (t : ℝ)
    (hE : ∀ i j, DifferentiableAt ℝ (fun s => E s i j) t)
    (hdet : (E t).det ≠ 0) (i j : Fin 4) :
    DifferentiableAt ℝ (fun s => (E s)⁻¹ i j) t := by
  have hinv := (jacobi_det_differentiableAt E t hE).inv hdet
  have hadj : DifferentiableAt ℝ (fun s => (E s).adjugate i j) t := by
    simp only [Matrix.adjugate_apply]
    apply jacobi_det_differentiableAt
    intro r a
    by_cases hr : r = j
    · subst r
      simpa only [Matrix.updateRow_self] using
        (differentiableAt_const _ : DifferentiableAt ℝ
          (fun _ : ℝ => (Pi.single i (1 : ℝ) : Fin 4 → ℝ) a) t)
    · simpa only [Matrix.updateRow_ne hr] using hE r a
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    using! hinv.mul hadj

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature matrix in any fixed chart. This transports the
actual curvature tensor; it does not require a diagonal or moving chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem normalized_frame_inverse (E G : Mat4)
    (hE : Eᵀ * G * E = 1) : E⁻¹ = Eᵀ * G := by
  have hdet := Matrix.isUnit_det_of_left_inverse hE
  have h := congrArg (fun A : Mat4 => A * E⁻¹) hE
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
    Matrix.one_mul] at h
  exact h.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Raising the momentum in the actual kinetic Hamiltonian gives the
ordinary tangent-coordinate geodesic field. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem inverse_rate_cancel (H C : Mat4) (p : Fin 4 → ℝ) :
    (-(C * H) - H * Cᵀ) *ᵥ p + H *ᵥ (Cᵀ *ᵥ p) = -(C *ᵥ (H *ᵥ p)) := by
  simp only [Matrix.sub_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  abel

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of the two derivative slots, in arbitrary coordinates
and in actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def twoFormSecondTrace (G : Mat4) (T : CovariantCoordinates 4) : CovariantCoordinates 2 :=
  fun v => ∑ a, ∑ b, G a b * T (Fin.cons a (Fin.cons b v))

end
end PositiveEinsteinFour.Geometry
end


section

/-! A local minimum of the actual energy forces the second derivative to
be nonnegative.  The finite-piece version cancels the chart boundary
terms before applying this elementary one-variable fact. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology BigOperators

noncomputable section

/-- The chartwise energy derivatives have the index sum as second
derivative after interior boundary matching and fixed endpoint jets. -/
theorem finite_piece_index_secondDeriv (n : ℕ) (E : ℕ → ℝ → ℝ)
    (I L R : ℕ → ℝ)
    (hfd : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i < n, DifferentiableAt ℝ (E i) s)
    (hD : ∀ i < n, HasDerivAt (deriv (E i)) (I i + R i - L i) 0)
    (hjoin : ∀ i < n, R i = L (i + 1)) (hleft : L 0 = 0) (hright : L n = 0) :
    HasDerivAt (deriv (fun s => ∑ i ∈ Finset.range n, E i s))
      (∑ i ∈ Finset.range n, I i) 0 := by
  have h := finite_piece_secondDeriv n E (fun i => I i + R i - L i) hfd hD
  have heq := finite_piece_boundary_cancellation n (fun i => I i + R i - L i)
    I L R (fun _ _ => rfl) hjoin
  rw [hleft, hright, add_zero, sub_zero] at heq
  rw [heq] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The connection-curvature contributions to the Euler and signature
local trace polynomials, with the actual covariant-slot convention. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def oneFormConnectionCurvatureMatrix (R : CovariantCoordinates 4) (i j : Fin 4) : Mat4 :=
  fun k l => -R ![i,j,k,l]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Reconstruct the actual base measure from its proved chart density.
The last identity is the normalized base input for the cotangent product. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

def riemannianChartFactor : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi ^ 2 / 32) * (euclideanHausdorffFactor : ℝ≥0∞)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exterior and trace tensors of a two-form covariant derivative.
Their norms are independent of the orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormExteriorTensor (A : CovariantCoordinates 3) : CovariantCoordinates 3 :=
  A - (fun v => A (v ∘ Equiv.swap 0 1)) +
    fun v => A (v ∘ (Equiv.swap 0 2).trans (Equiv.swap 0 1))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The kernel of the actual smooth scalar Laplacian.  The proof uses
the actual parallel-flow Green formula, full support of base volume, and
constancy along the complete geodesics.  No elliptic kernel theorem is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem scalar_tensor_square (T : CovariantCoordinates 1) :
    frameTensorSquareNorm T = ∑ i : Fin 4, T ![i] ^ 2 := by
  unfold frameTensorSquareNorm frameTensorPairing
  rw [sum_tensor_indices_cons]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_unique]
  have h (u : Fin 0 → Fin 4) : Fin.cons i u = ![i] := by
    funext j
    fin_cases j
    rfl
  rw [h, pow_two]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelDerivative
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.scalarCoordinateJet_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Sobolev regularity in four dimensions is characterized by the
four actual distributional coordinate derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem scalarDerivative_fourierMultiplier (i : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i u = (2 * Real.pi * Complex.I) •
      fourierMultiplierCLM ℂ (fun x : V => (x i : ℂ)) u := by
  rw [scalarCoordinateDerivative, lineDeriv_eq_fourierMultiplierCLM]
  congr 2
  ext x
  simp only [EuclideanSpace.inner_basisFun_real]

theorem scalarBessel_coordinate_term (i : Fin 4) (u : 𝓢'(V, ℂ)) :
    (2 * Real.pi * Complex.I)⁻¹ •
      fourierMultiplierCLM ℂ (scalarBesselCoordinate i) (scalarCoordinateDerivative i u) =
    fourierMultiplierCLM ℂ (fun x : V =>
      Complex.ofReal ((x i) ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))) u := by
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, OfNat.ofNat_ne_zero,
      Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true]
  rw [scalarDerivative_fourierMultiplier, map_smul, smul_smul,
    inv_mul_cancel₀ hc, one_smul,
    fourierMultiplierCLM_fourierMultiplierCLM_apply]
  · apply congrArg (fun f : V → ℂ => fourierMultiplierCLM ℂ f u)
    funext x
    simp only [Pi.mul_apply, scalarBesselCoordinate, ← Complex.ofReal_mul]
    congr 1
    ring
  · simp_rw [← EuclideanSpace.inner_basisFun_real]
    fun_prop
  · exact scalarBesselCoordinate_temperate i

/-- An exact bounded-multiplier reconstruction of one Bessel derivative. -/
theorem scalar_bessel_one_reconstruction (u : 𝓢'(V, ℂ)) :
    besselPotential V ℂ 1 u =
      fourierMultiplierCLM ℂ scalarBesselReciprocal u +
        ∑ i : Fin 4, (2 * Real.pi * Complex.I)⁻¹ •
          fourierMultiplierCLM ℂ (scalarBesselCoordinate i) (scalarCoordinateDerivative i u) := by
  simp_rw [scalarBessel_coordinate_term]
  rw [← scalar_fourierMultiplier_sum _ (by
    intro i
    simp_rw [← EuclideanSpace.inner_basisFun_real]
    fun_prop)]
  rw [← scalar_fourierMultiplier_add_p0 scalarBesselReciprocal_temperate (by
    apply Function.HasTemperateGrowth.sum
    intro i _
    simp_rw [← EuclideanSpace.inner_basisFun_real]
    fun_prop)]
  unfold besselPotential
  apply congrArg (fun f : V → ℂ => fourierMultiplierCLM ℂ f u)
  funext x
  have hnorm : ∑ i : Fin 4, (x i) ^ 2 = ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.inner_basisFun_real] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_sq_inner_left x
  simp only [scalarBesselReciprocal, ← Complex.ofReal_sum, ← Complex.ofReal_add]
  apply congrArg Complex.ofReal
  symm
  rw [← Finset.sum_mul, hnorm, ← one_add_mul]
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  calc
    (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) =
        (1 + ‖x‖ ^ 2) ^ (1 + (-1 / 2 : ℝ)) := by
      rw [Real.rpow_add hx, Real.rpow_one]
    _ = (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) := by norm_num

/-- Four coordinate derivatives characterize one additional Sobolev order. -/
theorem scalar_memSobolev_succ_iff (s : ℝ) (u : 𝓢'(V, ℂ)) :
    MemSobolev (s + 1) 2 u ↔
      MemSobolev s 2 u ∧ ∀ i : Fin 4, MemSobolev s 2 (scalarCoordinateDerivative i u) := by
  constructor
  · intro hu
    refine ⟨hu.mono (by linarith), fun i => ?_⟩
    simpa only [scalarCoordinateDerivative, add_sub_cancel_right] using
      (hu.lineDerivOp (m := EuclideanSpace.basisFun (Fin 4) ℝ i))
  · rintro ⟨hu, hD⟩
    rw [show s + 1 = 1 + s by ring, ← memSobolev_besselPotential_iff]
    rw [scalar_bessel_one_reconstruction]
    apply MemSobolev.add
    · exact hu.fourierMultiplierCLM_of_bounded scalarBesselReciprocal_temperate
        ⟨1, scalarBesselReciprocal_bound⟩
    · have hsum (S : Finset (Fin 4)) : MemSobolev s 2
          (∑ i ∈ S, (2 * Real.pi * Complex.I)⁻¹ •
            fourierMultiplierCLM ℂ (scalarBesselCoordinate i) (scalarCoordinateDerivative i u)) := by
        induction S using Finset.induction_on with
        | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero V ℂ s 2
        | @insert i S hi ih =>
            rw [Finset.sum_insert hi]
            exact ((hD i).fourierMultiplierCLM_of_bounded (scalarBesselCoordinate_temperate i)
              ⟨1, scalarBesselCoordinate_bound i⟩).smul _ |>.add ih
      exact hsum Finset.univ

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelBesselEstimate
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative L2 realization of the normalized Helmholtz inverse and its
first two coordinate derivatives. The constants retain Mathlib's `2π`
Fourier normalization. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

theorem scalar_derivative_multiplier (i : Fin 4) (a : V → ℂ)
    (ha : a.HasTemperateGrowth) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i (fourierMultiplierCLM ℂ a u) =
      (2 * Real.pi * Complex.I) •
        fourierMultiplierCLM ℂ (fun x => a x * (x i : ℂ)) u := by
  rw [scalarCoordinateDerivative, lineDeriv_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_fourierMultiplierCLM_apply ha (by fun_prop)]
  apply congrArg (fun b : V → ℂ =>
    (2 * Real.pi * Complex.I) • fourierMultiplierCLM ℂ b u)
  funext x
  simp only [Pi.mul_apply, EuclideanSpace.inner_basisFun_real]

theorem scalarBesselFirstL2_distribution (i : Fin 4) (f : L2) :
    (scalarBesselFirstL2 i f : 𝓢'(V, ℂ)) =
      scalarCoordinateDerivative i (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) := by
  rw [scalarBesselFirstL2_symbol, scalarBesselInverseL2_symbol,
    scalar_derivative_multiplier _ _ besselInverseSymbol_temperate]
  apply congrArg (fun a : V → ℂ =>
    (2 * Real.pi * Complex.I) • fourierMultiplierCLM ℂ a (f : 𝓢'(V, ℂ)))
  funext x
  simp only [besselFirstSymbol, besselInverseSymbol, ← Complex.ofReal_mul]
  congr 1
  ring

theorem scalarBesselSecondL2_distribution (i j : Fin 4) (f : L2) :
    (scalarBesselSecondL2 i j f : 𝓢'(V, ℂ)) =
      scalarCoordinateDerivative i
        (scalarCoordinateDerivative j (scalarBesselInverseL2 f : 𝓢'(V, ℂ))) := by
  rw [← scalarBesselFirstL2_distribution, scalarBesselFirstL2_symbol,
    scalarBesselSecondL2_symbol, scalarCoordinateDerivative, LineDeriv.lineDerivOp_smul]
  change _ = (2 * Real.pi * Complex.I) • scalarCoordinateDerivative i _
  rw [scalar_derivative_multiplier _ _ (besselFirstSymbol_temperate j),
    smul_smul, ← pow_two]
  apply congrArg (fun a : V → ℂ =>
    (2 * Real.pi * Complex.I) ^ 2 • fourierMultiplierCLM ℂ a (f : 𝓢'(V, ℂ)))
  funext x
  simp only [besselSecondSymbol, besselFirstSymbol, ← Complex.ofReal_mul]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelMultiplier
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compactly supported coefficients preserve every nonnegative
integer Sobolev order.  The proof uses the actual distributional product
rule and the coordinate-derivative characterization. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

/-- Leibniz's rule for the actual tempered-distribution coordinate derivative. -/
theorem scalarCoordinateDerivative_multiplier (a : 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ))
    (i : Fin 4) :
    scalarCoordinateDerivative i (smulLeftCLM ℂ a u) =
      smulLeftCLM ℂ (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)) u +
        smulLeftCLM ℂ a (scalarCoordinateDerivative i u) := by
  ext φ
  simp only [scalarCoordinateDerivative, lineDerivOp_apply_apply,
    smulLeftCLM_apply_apply, add_apply]
  rw [← map_add]
  congr 1
  rw [scalar_schwartz_coordinate_product]
  simp only [map_neg]
  module

/-- Every Schwartz coefficient preserves each integer Sobolev space. -/
theorem scalar_memSobolev_schwartz_multiplier (n : ℕ) (a : 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) (hu : MemSobolev (n : ℝ) 2 u) :
    MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ a u) := by
  induction n generalizing a u with
  | zero =>
      simpa only [Nat.cast_zero] using
        scalar_memSobolev_zero_multiplier a u (by simpa only [Nat.cast_zero] using hu)
  | succ n ih =>
      have hu' : MemSobolev (n : ℝ) 2 u ∧
          ∀ i : Fin 4, MemSobolev (n : ℝ) 2 (scalarCoordinateDerivative i u) := by
        apply (scalar_memSobolev_succ_iff (n : ℝ) u).mp
        simpa only [Nat.cast_add, Nat.cast_one] using hu
      have hbase := ih a u hu'.1
      have hderiv : ∀ i : Fin 4, MemSobolev (n : ℝ) 2
          (scalarCoordinateDerivative i (smulLeftCLM ℂ a u)) := by
        intro i
        rw [scalarCoordinateDerivative_multiplier]
        exact (ih (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)) u hu'.1).add
          (ih a (scalarCoordinateDerivative i u) (hu'.2 i))
      simpa only [Nat.cast_add, Nat.cast_one] using
        (scalar_memSobolev_succ_iff (n : ℝ) (smulLeftCLM ℂ a u)).mpr ⟨hbase, hderiv⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelCommutator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localization of the distributional Laplacian, and the loss of
only one Sobolev order in its smooth-cutoff commutator. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem scalar_secondDerivative_multiplier (a : 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) (i : Fin 4) :
    scalarCoordinateDerivative i (scalarCoordinateDerivative i (smulLeftCLM ℂ a u)) =
      smulLeftCLM ℂ a (scalarCoordinateDerivative i (scalarCoordinateDerivative i u)) +
      (2 : ℂ) • smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarCoordinateDerivative i u) +
      smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i
        (scalarSchwartzCoordinateDerivative i a)) u := by
  rw [scalarCoordinateDerivative_multiplier]
  change ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i}
    (smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) u +
      smulLeftCLM ℂ a (scalarCoordinateDerivative i u)) = _
  rw [LineDeriv.lineDerivOp_add]
  change scalarCoordinateDerivative i (smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) u) +
    scalarCoordinateDerivative i (smulLeftCLM ℂ a (scalarCoordinateDerivative i u)) = _
  rw [scalarCoordinateDerivative_multiplier, scalarCoordinateDerivative_multiplier]
  change smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i
      (scalarSchwartzCoordinateDerivative i a)) u +
      smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) (scalarCoordinateDerivative i u) +
    (smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) (scalarCoordinateDerivative i u) +
      smulLeftCLM ℂ a (scalarCoordinateDerivative i (scalarCoordinateDerivative i u))) = _
  module

/-- The actual distributional Laplacian product rule. -/
theorem scalar_laplacian_multiplier (a : 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) :
    Δ (smulLeftCLM ℂ a u) = smulLeftCLM ℂ a (Δ u) +
      (2 : ℂ) • (∑ i : Fin 4, smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarCoordinateDerivative i u)) + smulLeftCLM ℂ (Δ a : 𝓢(V, ℂ)) u := by
  have hu : (∑ i : Fin 4, smulLeftCLM ℂ a
      (scalarCoordinateDerivative i (scalarCoordinateDerivative i u))) =
        smulLeftCLM ℂ a (Δ u) := by
    rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ), map_sum]
    rfl
  have ha : (∑ i : Fin 4, smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i
      (scalarSchwartzCoordinateDerivative i a)) u) = smulLeftCLM ℂ (Δ a : 𝓢(V, ℂ)) u := by
    rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ),
      scalar_schwartz_sum_multiplier]
    rfl
  rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ)]
  change (∑ i : Fin 4, scalarCoordinateDerivative i
    (scalarCoordinateDerivative i (smulLeftCLM ℂ a u))) = _
  simp_rw [scalar_secondDerivative_multiplier]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, hu, ha]

theorem scalarLaplacianCommutator_eq (a : 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) :
    scalarLaplacianCommutator a u =
      (2 : ℂ) • (∑ i : Fin 4, smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarCoordinateDerivative i u)) + smulLeftCLM ℂ (Δ a : 𝓢(V, ℂ)) u := by
  rw [scalarLaplacianCommutator, scalar_laplacian_multiplier]
  abel

/-- A cutoff commutator loses only one derivative, including the H1-to-L2 case. -/
theorem scalarLaplacianCommutator_memSobolev (n : ℕ) (a : 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 u) :
    MemSobolev (n : ℝ) 2 (scalarLaplacianCommutator a u) := by
  have hu' : MemSobolev (n : ℝ) 2 u ∧
      ∀ i : Fin 4, MemSobolev (n : ℝ) 2 (scalarCoordinateDerivative i u) := by
    apply (scalar_memSobolev_succ_iff (n : ℝ) u).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hu
  have hsum (S : Finset (Fin 4)) : MemSobolev (n : ℝ) 2
      (∑ i ∈ S, smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarCoordinateDerivative i u)) := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero V ℂ (n : ℝ) 2
    | @insert i S hi ih =>
        rw [Finset.sum_insert hi]
        exact (scalar_memSobolev_schwartz_multiplier n
          (scalarSchwartzCoordinateDerivative i a) _ (hu'.2 i)).add ih
  rw [scalarLaplacianCommutator_eq]
  exact (hsum Finset.univ).smul _ |>.add
    (scalar_memSobolev_schwartz_multiplier n (Δ a : 𝓢(V, ℂ)) u hu'.1)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelPerturbation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative small-coefficient inverse on L2, with its actual
second-order distributional equation and H2 regularity. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

theorem scalarL2Perturbation_distribution
    (a : Fin 4 → Fin 4 → V → ℂ) (b : Fin 4 → V → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth) (hb : ∀ i, (b i).HasTemperateGrowth)
    (haLp : ∀ i j, MemLp (a i j) ∞ (volume : Measure V))
    (hbLp : ∀ i, MemLp (b i) ∞ (volume : Measure V)) (f : L2) :
    (scalarL2Perturbation (fun i j => (haLp i j).toLp _) (fun i => (hbLp i).toLp _) f :
        𝓢'(V, ℂ)) =
      (∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (a i j)
        (scalarCoordinateDerivative i
          (scalarCoordinateDerivative j (scalarBesselInverseL2 f : 𝓢'(V, ℂ))))) +
      ∑ i : Fin 4, smulLeftCLM ℂ (b i)
        (scalarCoordinateDerivative i (scalarBesselInverseL2 f : 𝓢'(V, ℂ))) := by
  have hsecond (i j : Fin 4) :
      (scalarL2Multiply ((haLp i j).toLp _) (scalarBesselSecondL2 i j f) : 𝓢'(V, ℂ)) =
        smulLeftCLM ℂ (a i j) (scalarCoordinateDerivative i
          (scalarCoordinateDerivative j (scalarBesselInverseL2 f : 𝓢'(V, ℂ)))) := by
    rw [scalarL2Multiply_distribution _ (ha i j), scalarBesselSecondL2_distribution]
  have hfirst (i : Fin 4) :
      (scalarL2Multiply ((hbLp i).toLp _) (scalarBesselFirstL2 i f) : 𝓢'(V, ℂ)) =
        smulLeftCLM ℂ (b i) (scalarCoordinateDerivative i
          (scalarBesselInverseL2 f : 𝓢'(V, ℂ))) := by
    rw [scalarL2Multiply_distribution _ (hb i), scalarBesselFirstL2_distribution]
  rw [scalarL2Perturbation_apply]
  change Lp.toTemperedDistributionCLM ℂ volume 2 _ = _
  simp only [map_add, map_sum, Lp.toTemperedDistributionCLM_apply, hsecond, hfirst]

/-- Small smooth bounded coefficients give a genuine H2 solution of the
perturbed distributional equation. No regularity of a prospective solution
is used in this construction. -/
theorem scalar_perturbedHelmholtz_solution
    (a : Fin 4 → Fin 4 → V → ℂ) (b : Fin 4 → V → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth) (hb : ∀ i, (b i).HasTemperateGrowth)
    (δ : ℝ) (haBound : ∀ i j x, ‖a i j x‖ ≤ δ) (hbBound : ∀ i x, ‖b i x‖ ≤ δ)
    (hsmall : 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ < 1) (f : L2) :
    ∃ u : L2, MemSobolev 2 2 (u : 𝓢'(V, ℂ)) ∧
      normalizedScalarHelmholtz (u : 𝓢'(V, ℂ)) +
        (∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (a i j)
          (scalarCoordinateDerivative i (scalarCoordinateDerivative j (u : 𝓢'(V, ℂ))))) +
        (∑ i : Fin 4, smulLeftCLM ℂ (b i)
          (scalarCoordinateDerivative i (u : 𝓢'(V, ℂ)))) = (f : 𝓢'(V, ℂ)) := by
  let haLp := fun i j => scalarCoefficient_memLp (a i j) (ha i j) δ (haBound i j)
  let hbLp := fun i => scalarCoefficient_memLp (b i) (hb i) δ (hbBound i)
  obtain ⟨v, hv, _⟩ := scalarL2Perturbation_existsUnique
    (fun i j => (haLp i j).toLp _) (fun i => (hbLp i).toLp _) δ
    (fun i j => scalarCoefficient_Linf_bound _ _ δ (haBound i j))
    (fun i => scalarCoefficient_Linf_bound _ _ δ (hbBound i)) hsmall f
  refine ⟨scalarBesselInverseL2 v, scalarBesselInverseL2_memSobolev v, ?_⟩
  have h := congrArg (Lp.toTemperedDistributionCLM ℂ volume 2) hv
  rw [map_add, Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistributionCLM_apply,
    Lp.toTemperedDistributionCLM_apply,
    scalarL2Perturbation_distribution a b ha hb haLp hbLp v] at h
  rw [scalarBesselInverseL2_helmholtz, add_assoc]
  exact h

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelAdjoint
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.scalarCoordinateJet_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual transpose of the localized second-order scalar operator.
All coefficient and derivative operations here act on Schwartz functions;
there is no assumed integration-by-parts or regularity identity. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

/-- The actual variable-coefficient operator on tempered distributions. -/
def scalarPerturbedOperator (a : Fin 4 → Fin 4 → 𝓢(V, ℂ))
    (b : Fin 4 → 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) : 𝓢'(V, ℂ) :=
  normalizedScalarHelmholtz u +
    (∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (a i j)
      (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) +
    ∑ i : Fin 4, smulLeftCLM ℂ (b i) (scalarCoordinateDerivative i u)

/-- The transpose includes the derivatives of the coefficients. -/
def scalarSchwartzTranspose (a : Fin 4 → Fin 4 → 𝓢(V, ℂ))
    (b : Fin 4 → 𝓢(V, ℂ)) (φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  scalarSchwartzHelmholtz φ +
    (∑ i : Fin 4, ∑ j : Fin 4,
      scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i
        (SchwartzMap.smulLeftCLM ℂ (a i j) φ))) -
    ∑ i : Fin 4, scalarSchwartzCoordinateDerivative i
      (SchwartzMap.smulLeftCLM ℂ (b i) φ)

theorem scalar_second_transpose (i j : Fin 4) (u : 𝓢'(V, ℂ))
    (φ : 𝓢(V, ℂ)) :
    scalarCoordinateDerivative i (scalarCoordinateDerivative j u) φ =
      u (scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i φ)) := by
  simp [scalarCoordinateDerivative, scalarSchwartzCoordinateDerivative,
    LineDeriv.lineDerivOp_neg]

/-- The precise distributional transpose identity, including signs and the
order reversal in the two derivative slots. -/
theorem scalarPerturbedOperator_transpose (a : Fin 4 → Fin 4 → 𝓢(V, ℂ))
    (b : Fin 4 → 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) (φ : 𝓢(V, ℂ)) :
    scalarPerturbedOperator a b u φ = u (scalarSchwartzTranspose a b φ) := by
  simp only [scalarPerturbedOperator, scalarSchwartzTranspose,
    add_apply, sum_apply, smulLeftCLM_apply_apply, scalar_second_transpose,
    scalarSchwartzHelmholtz_transpose, map_add, map_sub, map_sum]
  simp only [scalarCoordinateDerivative, scalarSchwartzCoordinateDerivative,
    lineDerivOp_apply_apply, map_neg]
  rw [Finset.sum_neg_distrib]
  abel

/-- First-order product rule on the test-function space. -/
theorem scalarSchwartzCoordinateDerivative_product (a φ : 𝓢(V, ℂ)) (i : Fin 4) :
    scalarSchwartzCoordinateDerivative i (SchwartzMap.smulLeftCLM ℂ a φ) =
      SchwartzMap.smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) φ +
        SchwartzMap.smulLeftCLM ℂ a (scalarSchwartzCoordinateDerivative i φ) := by
  ext x
  simp only [scalarSchwartzCoordinateDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply a.hasTemperateGrowth, smul_eq_mul]
  rw [fderiv_fun_mul a.differentiableAt φ.differentiableAt]
  simp only [add_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)).hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  ring

/-- Expanding the two coefficient derivatives exhibits all lower-order terms. -/
theorem scalarSchwartzCoordinateDerivative_second_product
    (a φ : 𝓢(V, ℂ)) (i j : Fin 4) :
    scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i
      (SchwartzMap.smulLeftCLM ℂ a φ)) =
      SchwartzMap.smulLeftCLM ℂ a
        (scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i φ)) +
      SchwartzMap.smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarSchwartzCoordinateDerivative j φ) +
      SchwartzMap.smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative j a)
        (scalarSchwartzCoordinateDerivative i φ) +
      SchwartzMap.smulLeftCLM ℂ
        (scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i a)) φ := by
  rw [scalarSchwartzCoordinateDerivative_product]
  change ∂_{EuclideanSpace.basisFun (Fin 4) ℝ j} (_ + _) = _
  rw [LineDeriv.lineDerivOp_add]
  change scalarSchwartzCoordinateDerivative j _ + scalarSchwartzCoordinateDerivative j _ = _
  rw [scalarSchwartzCoordinateDerivative_product, scalarSchwartzCoordinateDerivative_product]
  abel

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelUniqueness
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density step for distributional uniqueness. An invertible L2
extension of the transposed operator after Bessel regularization gives a
dense Schwartz range, and hence a trivial L2 distributional kernel. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

/-- A transposed L2 isomorphism gives distributional uniqueness without
regularity of the kernel element. -/
theorem scalarPerturbedOperator_kernel_of_transpose_equiv
    (a : Fin 4 → Fin 4 → 𝓢(V, ℂ)) (b : Fin 4 → 𝓢(V, ℂ))
    (e : L2 ≃L[ℂ] L2)
    (he : ∀ φ : 𝓢(V, ℂ),
      (scalarSchwartzTranspose a b (scalarSchwartzBesselInverse φ)).toLp 2 = e (φ.toLp 2))
    (u : L2) (hu : scalarPerturbedOperator a b (u : 𝓢'(V, ℂ)) = 0) : u = 0 := by
  apply scalarL2_eq_zero_of_dense_tests u (scalarSchwartzTranspose a b)
    (scalarSchwartz_denseRange_of_bessel_equiv _ e he)
  intro φ
  rw [← scalarPerturbedOperator_transpose, hu]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelAdjointEstimate
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative bounded extension of the actual transposed operator after
Bessel regularization. Coefficient bounds imply the dense-range condition used for
distributional uniqueness. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal LineDeriv BigOperators Laplacian

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

theorem scalar_derivative_schwartz_distribution (i : Fin 4) (φ : S) :
    scalarCoordinateDerivative i (φ : 𝓢'(V, ℂ)) = (D i φ : 𝓢'(V, ℂ)) :=
  lineDerivOp_toTemperedDistributionCLM_eq φ (EuclideanSpace.basisFun (Fin 4) ℝ i)

theorem scalarBesselFirstL2_schwartz_distribution (i : Fin 4) (φ : S) :
    (scalarBesselFirstL2 i (φ.toLp 2 volume) : 𝓢'(V, ℂ)) =
      (D i (scalarSchwartzBesselInverse φ) : 𝓢'(V, ℂ)) := by
  rw [scalarBesselFirstL2_distribution, ← scalarSchwartzBesselInverse_toLp,
    Lp.toTemperedDistribution_toLp_eq, scalar_derivative_schwartz_distribution]

theorem scalarBesselFirstL2_toLp (i : Fin 4) (φ : S) :
    scalarBesselFirstL2 i (φ.toLp 2 volume) =
      (D i (scalarSchwartzBesselInverse φ)).toLp 2 volume :=
  scalarL2_eq_schwartz _ _ (scalarBesselFirstL2_schwartz_distribution i φ)

theorem scalarBesselSecondL2_schwartz_distribution (i j : Fin 4) (φ : S) :
    (scalarBesselSecondL2 i j (φ.toLp 2 volume) : 𝓢'(V, ℂ)) =
      (D i (D j (scalarSchwartzBesselInverse φ)) : 𝓢'(V, ℂ)) := by
  rw [scalarBesselSecondL2_distribution, ← scalarSchwartzBesselInverse_toLp,
    Lp.toTemperedDistribution_toLp_eq, scalar_derivative_schwartz_distribution,
    scalar_derivative_schwartz_distribution]

theorem scalarBesselSecondL2_toLp (i j : Fin 4) (φ : S) :
    scalarBesselSecondL2 i j (φ.toLp 2 volume) =
      (D i (D j (scalarSchwartzBesselInverse φ))).toLp 2 volume :=
  scalarL2_eq_schwartz _ _ (scalarBesselSecondL2_schwartz_distribution i j φ)

def scalarAdjointSecondPiece (a φ : S) (i j : Fin 4) : S :=
  SchwartzMap.smulLeftCLM ℂ a (D j (D i φ)) +
    SchwartzMap.smulLeftCLM ℂ (D i a) (D j φ) +
    SchwartzMap.smulLeftCLM ℂ (D j a) (D i φ) +
    SchwartzMap.smulLeftCLM ℂ (D j (D i a)) φ

def scalarAdjointFirstPiece (b φ : S) (i : Fin 4) : S :=
  SchwartzMap.smulLeftCLM ℂ b (D i φ) + SchwartzMap.smulLeftCLM ℂ (D i b) φ

def scalarAdjointSecondL2Term (a : S) (i j : Fin 4) : L2 →L[ℂ] L2 :=
  (scalarSchwartzMultiplyL2 a).comp (scalarBesselSecondL2 j i) +
    (scalarSchwartzMultiplyL2 (D i a)).comp (scalarBesselFirstL2 j) +
    (scalarSchwartzMultiplyL2 (D j a)).comp (scalarBesselFirstL2 i) +
    (scalarSchwartzMultiplyL2 (D j (D i a))).comp scalarBesselInverseL2

def scalarAdjointFirstL2Term (b : S) (i : Fin 4) : L2 →L[ℂ] L2 :=
  (scalarSchwartzMultiplyL2 b).comp (scalarBesselFirstL2 i) +
    (scalarSchwartzMultiplyL2 (D i b)).comp scalarBesselInverseL2

def scalarAdjointL2Perturbation (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) : L2 →L[ℂ] L2 :=
  (∑ i : Fin 4, ∑ j : Fin 4, scalarAdjointSecondL2Term (a i j) i j) -
    ∑ i : Fin 4, scalarAdjointFirstL2Term (b i) i

theorem scalarAdjointSecondL2Term_toLp (a φ : S) (i j : Fin 4) :
    scalarAdjointSecondL2Term a i j (φ.toLp 2 volume) =
      (scalarAdjointSecondPiece a (scalarSchwartzBesselInverse φ) i j).toLp 2 volume := by
  simp only [scalarAdjointSecondL2Term, add_apply, ContinuousLinearMap.comp_apply,
    scalarBesselSecondL2_toLp, scalarBesselFirstL2_toLp, ← scalarSchwartzBesselInverse_toLp,
    scalarSchwartzMultiplyL2_toLp]
  simp only [scalarAdjointSecondPiece, ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (μ := (volume : Measure V)), map_add]

theorem scalarAdjointFirstL2Term_toLp (b φ : S) (i : Fin 4) :
    scalarAdjointFirstL2Term b i (φ.toLp 2 volume) =
      (scalarAdjointFirstPiece b (scalarSchwartzBesselInverse φ) i).toLp 2 volume := by
  simp only [scalarAdjointFirstL2Term, add_apply, ContinuousLinearMap.comp_apply,
    scalarBesselFirstL2_toLp, ← scalarSchwartzBesselInverse_toLp,
    scalarSchwartzMultiplyL2_toLp]
  simp only [scalarAdjointFirstPiece, ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (μ := (volume : Measure V)), map_add]

/-- The bounded L2 perturbation is exactly the regularized formal transpose. -/
theorem scalarAdjointL2Perturbation_toLp (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (φ : S) :
    (scalarSchwartzTranspose a b (scalarSchwartzBesselInverse φ)).toLp 2 volume =
      φ.toLp 2 volume + scalarAdjointL2Perturbation a b (φ.toLp 2 volume) := by
  have hT : scalarSchwartzTranspose a b (scalarSchwartzBesselInverse φ) =
      scalarSchwartzHelmholtz (scalarSchwartzBesselInverse φ) +
        (∑ i : Fin 4, ∑ j : Fin 4,
          scalarAdjointSecondPiece (a i j) (scalarSchwartzBesselInverse φ) i j) -
        ∑ i : Fin 4, scalarAdjointFirstPiece (b i) (scalarSchwartzBesselInverse φ) i := by
    unfold scalarSchwartzTranspose
    simp only [scalarSchwartzCoordinateDerivative_second_product]
    simp only [scalarSchwartzCoordinateDerivative_product]
    simp only [scalarAdjointSecondPiece, scalarAdjointFirstPiece]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    abel
  rw [hT]
  change (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ = _
  rw [map_sub, map_add, map_sum]
  simp only [map_sum]
  change (scalarSchwartzHelmholtz (scalarSchwartzBesselInverse φ)).toLp 2 volume +
      (∑ i : Fin 4, ∑ j : Fin 4,
        (scalarAdjointSecondPiece (a i j) (scalarSchwartzBesselInverse φ) i j).toLp 2 volume) -
      (∑ i : Fin 4, (scalarAdjointFirstPiece (b i) (scalarSchwartzBesselInverse φ) i).toLp 2 volume) = _
  rw [scalarSchwartzHelmholtz_bessel_toLp]
  simp only [scalarAdjointL2Perturbation, sub_apply, sum_apply,
    scalarAdjointSecondL2Term_toLp, scalarAdjointFirstL2Term_toLp]
  abel

theorem scalarAdjointSecondL2Term_bound (a : S) (i j : Fin 4) (δ : ℝ)
    (hδ : 0 ≤ δ) (ha : ‖a.toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hi : ‖(D i a).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hj : ‖(D j a).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hij : ‖(D j (D i a)).toLp ∞ (volume : Measure V)‖ ≤ δ) (f : L2) :
    ‖scalarAdjointSecondL2Term a i j f‖ ≤
      δ * ((2 * Real.pi) ^ 2 + 2 * (2 * Real.pi) + 1) * ‖f‖ := by
  let A := scalarSchwartzMultiplyL2 a (scalarBesselSecondL2 j i f)
  let B := scalarSchwartzMultiplyL2 (D i a) (scalarBesselFirstL2 j f)
  let C := scalarSchwartzMultiplyL2 (D j a) (scalarBesselFirstL2 i f)
  let E := scalarSchwartzMultiplyL2 (D j (D i a)) (scalarBesselInverseL2 f)
  have hA : ‖A‖ ≤ δ * ((2 * Real.pi) ^ 2 * ‖f‖) :=
    (scalarSchwartzMultiplyL2_bound _ _ ha _).trans
      (mul_le_mul_of_nonneg_left (scalarBesselSecondL2_norm j i f) hδ)
  have hB : ‖B‖ ≤ δ * ((2 * Real.pi) * ‖f‖) :=
    (scalarSchwartzMultiplyL2_bound _ _ hi _).trans
      (mul_le_mul_of_nonneg_left (scalarBesselFirstL2_norm j f) hδ)
  have hC : ‖C‖ ≤ δ * ((2 * Real.pi) * ‖f‖) :=
    (scalarSchwartzMultiplyL2_bound _ _ hj _).trans
      (mul_le_mul_of_nonneg_left (scalarBesselFirstL2_norm i f) hδ)
  have hE : ‖E‖ ≤ δ * ‖f‖ :=
    (scalarSchwartzMultiplyL2_bound _ _ hij _).trans
      (mul_le_mul_of_nonneg_left (scalarBesselInverseL2_norm f) hδ)
  change ‖A + B + C + E‖ ≤ _
  have hAB := norm_add_le A B
  have hABC := norm_add_le (A + B) C
  have hABCE := norm_add_le (A + B + C) E
  nlinarith

theorem scalarAdjointFirstL2Term_bound (b : S) (i : Fin 4) (δ : ℝ)
    (hδ : 0 ≤ δ) (hb : ‖b.toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hi : ‖(D i b).toLp ∞ (volume : Measure V)‖ ≤ δ) (f : L2) :
    ‖scalarAdjointFirstL2Term b i f‖ ≤ δ * ((2 * Real.pi) + 1) * ‖f‖ := by
  have hB := (scalarSchwartzMultiplyL2_bound _ _ hb (scalarBesselFirstL2 i f)).trans
    (mul_le_mul_of_nonneg_left (scalarBesselFirstL2_norm i f) hδ)
  have hI := (scalarSchwartzMultiplyL2_bound _ _ hi (scalarBesselInverseL2 f)).trans
    (mul_le_mul_of_nonneg_left (scalarBesselInverseL2_norm f) hδ)
  change ‖scalarSchwartzMultiplyL2 b (scalarBesselFirstL2 i f) +
    scalarSchwartzMultiplyL2 (D i b) (scalarBesselInverseL2 f)‖ ≤ _
  have hadd := norm_add_le (scalarSchwartzMultiplyL2 b (scalarBesselFirstL2 i f))
    (scalarSchwartzMultiplyL2 (D i b) (scalarBesselInverseL2 f))
  nlinarith

/-- Uniform control of coefficient derivatives makes the formal transpose
an explicit small perturbation. -/
theorem scalarAdjointL2Perturbation_bound (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j, ‖(a i j).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha1 : ∀ i j k, ‖(D k (a i j)).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha2 : ∀ i j k l, ‖(D k (D l (a i j))).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb : ∀ i, ‖(b i).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb1 : ∀ i k, ‖(D k (b i)).toLp ∞ (volume : Measure V)‖ ≤ δ) :
    ∀ f : L2, ‖scalarAdjointL2Perturbation a b f‖ ≤
      ((16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ) * ‖f‖ := by
  intro f
  simp only [scalarAdjointL2Perturbation, sub_apply, sum_apply]
  calc
    _ ≤ (∑ i : Fin 4, ∑ j : Fin 4, ‖scalarAdjointSecondL2Term (a i j) i j f‖) +
        ∑ i : Fin 4, ‖scalarAdjointFirstL2Term (b i) i f‖ := by
      apply (norm_sub_le _ _).trans
      apply add_le_add
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      · exact norm_sum_le _ _
    _ ≤ (∑ _i : Fin 4, ∑ _j : Fin 4,
          δ * ((2 * Real.pi) ^ 2 + 2 * (2 * Real.pi) + 1) * ‖f‖) +
        ∑ _i : Fin 4, δ * ((2 * Real.pi) + 1) * ‖f‖ := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          scalarAdjointSecondL2Term_bound _ i j δ hδ (ha i j) (ha1 i j i)
            (ha1 i j j) (ha2 i j j i) f))
      · exact Finset.sum_le_sum (fun i _ =>
          scalarAdjointFirstL2Term_bound _ i δ hδ (hb i) (hb1 i i) f)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem scalarAdjointL2Perturbation_opNorm (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j, ‖(a i j).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha1 : ∀ i j k, ‖(D k (a i j)).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha2 : ∀ i j k l, ‖(D k (D l (a i j))).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb : ∀ i, ‖(b i).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb1 : ∀ i k, ‖(D k (b i)).toLp ∞ (volume : Measure V)‖ ≤ δ) :
    ‖scalarAdjointL2Perturbation a b‖ ≤
      (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ := by
  exact (scalarAdjointL2Perturbation a b).opNorm_le_bound (by positivity)
    (scalarAdjointL2Perturbation_bound a b δ hδ ha ha1 ha2 hb hb1)

/-- An actual L2 distributional kernel element vanishes under explicit
smallness of the coefficient jets through order two. -/
theorem scalarPerturbedOperator_kernel_small (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j, ‖(a i j).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha1 : ∀ i j k, ‖(D k (a i j)).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (ha2 : ∀ i j k l, ‖(D k (D l (a i j))).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb : ∀ i, ‖(b i).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hb1 : ∀ i k, ‖(D k (b i)).toLp ∞ (volume : Measure V)‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u : L2) (hu : scalarPerturbedOperator a b (u : 𝓢'(V, ℂ)) = 0) : u = 0 := by
  have hK := (scalarAdjointL2Perturbation_opNorm a b δ hδ ha ha1 ha2 hb hb1).trans_lt hsmall
  apply scalarPerturbedOperator_kernel_of_transpose_equiv a b
    (scalarPerturbationEquiv (scalarAdjointL2Perturbation a b) hK) _ u hu
  intro φ
  rw [scalarAdjointL2Perturbation_toLp, scalarPerturbationEquiv_apply]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelLocalRegularity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-coefficient regularity applies to an existing L2 distributional
solution: construct an H2 solution, then identify the two using the actual
formal-transpose uniqueness theorem. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

theorem scalar_coordinate_sub (i : Fin 4) (u v : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i (u - v) =
      scalarCoordinateDerivative i u - scalarCoordinateDerivative i v := by
  exact (LineDeriv.lineDerivOpCLM ℂ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ i)).map_sub u v

theorem scalarPerturbedOperator_sub (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (u v : 𝓢'(V, ℂ)) :
    scalarPerturbedOperator a b (u - v) =
      scalarPerturbedOperator a b u - scalarPerturbedOperator a b v := by
  simp only [scalarPerturbedOperator, normalizedScalarHelmholtz, scalar_coordinate_sub,
    ← laplacianCLM_apply, map_sub, smul_sub, Finset.sum_sub_distrib]
  abel

/-- This is regularity of the given solution, not only existence of a new
regular solution. All smallness assumptions concern the actual coefficient
functions and their first two derivatives. -/
theorem scalar_small_elliptic_gain_two
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u f : L2) (hu : scalarPerturbedOperator a b (u : 𝓢'(V, ℂ)) = (f : 𝓢'(V, ℂ))) :
    MemSobolev 2 2 (u : 𝓢'(V, ℂ)) := by
  have hsmall' : 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ < 1 := by
    have hle : 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ ≤
        (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ := by
      calc
        _ ≤ 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ +
            (32 * (2 * Real.pi) + 20) * δ := by
          exact le_add_of_nonneg_right (mul_nonneg (by positivity) hδ)
        _ = _ := by ring
    exact hle.trans_lt hsmall
  obtain ⟨v, hv2, hv⟩ := scalar_perturbedHelmholtz_solution
    (fun i j => (a i j : V → ℂ)) (fun i => (b i : V → ℂ))
    (fun i j => (a i j).hasTemperateGrowth) (fun i => (b i).hasTemperateGrowth)
    δ ha hb hsmall' f
  have hv' : scalarPerturbedOperator a b (v : 𝓢'(V, ℂ)) = (f : 𝓢'(V, ℂ)) := hv
  have hdiff : scalarPerturbedOperator a b ((u - v : L2) : 𝓢'(V, ℂ)) = 0 := by
    change scalarPerturbedOperator a b ((Lp.toTemperedDistributionCLM ℂ volume 2) (u - v)) = 0
    rw [map_sub, scalarPerturbedOperator_sub, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistributionCLM_apply, hu, hv', sub_self]
  have heq : u - v = 0 := scalarPerturbedOperator_kernel_small a b δ hδ
    (fun i j => scalarSchwartz_Linf_bound _ δ hδ (ha i j))
    (fun i j k => scalarSchwartz_Linf_bound _ δ hδ (ha1 i j k))
    (fun i j k l => scalarSchwartz_Linf_bound _ δ hδ (ha2 i j k l))
    (fun i => scalarSchwartz_Linf_bound _ δ hδ (hb i))
    (fun i k => scalarSchwartz_Linf_bound _ δ hδ (hb1 i k)) hsmall (u - v) hdiff
  rw [sub_eq_zero.mp heq]
  exact hv2

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelBootstrap
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.scalarCoordinateJet_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer-order elliptic bootstrap from the actual distributional
commutator and the proved small-coefficient H2 regularity theorem. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

theorem scalar_derivative_fourier (i : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i u = (2 * Real.pi * Complex.I) •
      fourierMultiplierCLM ℂ (fun x : V => (x i : ℂ)) u := by
  rw [scalarCoordinateDerivative, lineDeriv_eq_fourierMultiplierCLM]
  apply congrArg (fun a : V → ℂ => (2 * Real.pi * Complex.I) • fourierMultiplierCLM ℂ a u)
  funext x
  simp only [EuclideanSpace.inner_basisFun_real]

/-- Coordinate derivatives commute for every tempered distribution. -/
theorem scalarCoordinateDerivative_commute (i j : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i (scalarCoordinateDerivative j u) =
      scalarCoordinateDerivative j (scalarCoordinateDerivative i u) := by
  simp_rw [scalar_derivative_fourier, map_smul, smul_smul]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by
      simp_rw [← EuclideanSpace.inner_basisFun_real]; fun_prop) (by
      simp_rw [← EuclideanSpace.inner_basisFun_real]; fun_prop),
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by
      simp_rw [← EuclideanSpace.inner_basisFun_real]; fun_prop) (by
      simp_rw [← EuclideanSpace.inner_basisFun_real]; fun_prop)]
  apply congrArg (fun a : V → ℂ =>
    ((2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I)) • fourierMultiplierCLM ℂ a u)
  funext x
  simp only [Pi.mul_apply, mul_comm]

theorem scalar_derivative_add (k : Fin 4) (u v : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (u + v) =
      scalarCoordinateDerivative k u + scalarCoordinateDerivative k v :=
  (LineDeriv.lineDerivOpCLM ℂ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ k)).map_add u v

theorem scalar_derivative_sub (k : Fin 4) (u v : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (u - v) =
      scalarCoordinateDerivative k u - scalarCoordinateDerivative k v :=
  (LineDeriv.lineDerivOpCLM ℂ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ k)).map_sub u v

theorem scalar_derivative_real_smul (k : Fin 4) (c : ℝ) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (c • u) = c • scalarCoordinateDerivative k u :=
  (LineDeriv.lineDerivOpCLM ℝ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ k)).map_smul c u

theorem scalar_derivative_sum (k : Fin 4) (u : Fin 4 → 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (∑ i, u i) = ∑ i, scalarCoordinateDerivative k (u i) :=
  map_sum (LineDeriv.lineDerivOpCLM ℂ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ k)) u Finset.univ

theorem scalar_derivative_laplacian (k : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (Δ u) = Δ (scalarCoordinateDerivative k u) := by
  rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ),
    TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ)]
  change scalarCoordinateDerivative k (∑ i : Fin 4,
    scalarCoordinateDerivative i (scalarCoordinateDerivative i u)) =
      ∑ i : Fin 4, scalarCoordinateDerivative i
        (scalarCoordinateDerivative i (scalarCoordinateDerivative k u))
  rw [scalar_derivative_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarCoordinateDerivative_commute k i, scalarCoordinateDerivative_commute k i]

theorem scalar_derivative_helmholtz (k : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (normalizedScalarHelmholtz u) =
      normalizedScalarHelmholtz (scalarCoordinateDerivative k u) := by
  rw [normalizedScalarHelmholtz, normalizedScalarHelmholtz,
    scalar_derivative_sub, scalar_derivative_real_smul, scalar_derivative_laplacian]

/-- Exact first commutator of the variable-coefficient operator. -/
theorem scalarPerturbedOperator_derivative (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (k : Fin 4) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative k (scalarPerturbedOperator a b u) =
      scalarPerturbedOperator a b (scalarCoordinateDerivative k u) +
        (∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (D k (a i j))
          (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) +
        ∑ i : Fin 4, smulLeftCLM ℂ (D k (b i)) (scalarCoordinateDerivative i u) := by
  have hcomm (i j : Fin 4) :
      scalarCoordinateDerivative k (scalarCoordinateDerivative i (scalarCoordinateDerivative j u)) =
        scalarCoordinateDerivative i (scalarCoordinateDerivative j (scalarCoordinateDerivative k u)) := by
    rw [scalarCoordinateDerivative_commute k i, scalarCoordinateDerivative_commute k j]
  have hcomm1 (i : Fin 4) : scalarCoordinateDerivative k (scalarCoordinateDerivative i u) =
      scalarCoordinateDerivative i (scalarCoordinateDerivative k u) :=
    scalarCoordinateDerivative_commute k i u
  simp only [scalarPerturbedOperator, scalar_derivative_add, scalar_derivative_helmholtz,
    scalar_derivative_sum, scalarCoordinateDerivative_multiplier, scalarSchwartzCoordinateDerivative,
    hcomm, hcomm1,
    Finset.sum_add_distrib]
  abel

theorem scalar_sobolev_nat_step (n : ℕ) (u : 𝓢'(V, ℂ)) :
    MemSobolev ((n + 1 : ℕ) : ℝ) 2 u ↔ MemSobolev (n : ℝ) 2 u ∧
      ∀ i : Fin 4, MemSobolev (n : ℝ) 2 (scalarCoordinateDerivative i u) := by
  simpa only [Nat.cast_add, Nat.cast_one] using scalar_memSobolev_succ_iff (n : ℝ) u

/-- Every integer Sobolev order of the right-hand side gives two additional
orders for the original L2 solution. -/
theorem scalar_small_elliptic_integer_regularity
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (n : ℕ) (u f : 𝓢'(V, ℂ)) (hu : MemSobolev 0 2 u)
    (hf : MemSobolev (n : ℝ) 2 f) (heq : scalarPerturbedOperator a b u = f) :
    MemSobolev ((n + 2 : ℕ) : ℝ) 2 u := by
  induction n generalizing u f with
  | zero =>
      obtain ⟨u, rfl⟩ := memSobolev_zero_iff.mp hu
      obtain ⟨f, rfl⟩ := memSobolev_zero_iff.mp (by simpa only [Nat.cast_zero] using hf)
      simpa using scalar_small_elliptic_gain_two a b δ hδ ha ha1 ha2 hb hb1 hsmall u f heq
  | succ n ih =>
      have hfstep := (scalar_sobolev_nat_step n f).mp hf
      have hu2 := ih u f hu hfstep.1 heq
      have hustep := (scalar_sobolev_nat_step (n + 1) u).mp hu2
      have hD (k : Fin 4) := (scalar_sobolev_nat_step n (scalarCoordinateDerivative k u)).mp
        (hustep.2 k)
      have hderiv (k : Fin 4) :
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (scalarCoordinateDerivative k u) := by
        let A : 𝓢'(V, ℂ) := ∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (D k (a i j))
          (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))
        let B : 𝓢'(V, ℂ) := ∑ i : Fin 4, smulLeftCLM ℂ (D k (b i))
          (scalarCoordinateDerivative i u)
        have hA : MemSobolev (n : ℝ) 2 A := by
          apply scalar_sobolev_sum_p0 n
          intro i
          apply scalar_sobolev_sum_p0 n
          intro j
          exact scalar_memSobolev_schwartz_multiplier n _ _ ((hD j).2 i)
        have hB : MemSobolev (n : ℝ) 2 B := by
          apply scalar_sobolev_sum_p0 n
          intro i
          exact scalar_memSobolev_schwartz_multiplier n _ _ (hD i).1
        have hEq : scalarPerturbedOperator a b (scalarCoordinateDerivative k u) =
            scalarCoordinateDerivative k f - A - B := by
          calc
            _ = (scalarPerturbedOperator a b (scalarCoordinateDerivative k u) + A + B) - A - B := by abel
            _ = _ := by rw [← scalarPerturbedOperator_derivative, heq]
        exact ih _ _ ((hustep.2 k).mono (by positivity)) ((hfstep.2 k).sub hA |>.sub hB) hEq
      simpa only [Nat.add_assoc] using
        (scalar_sobolev_nat_step (n + 2) u).mpr ⟨hu2, hderiv⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarAdjointCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density-weighted chart equation gives the formal adjoint of the
nondivergence operator. Its expansion has the same principal coefficients,
a differentiated drift, and an explicit smooth zeroth-order potential. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

def scalarFormalAdjointOperator (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (u : T) : T :=
  normalizedScalarHelmholtz u +
    (∑ i, ∑ j, scalarCoordinateDerivative j (scalarCoordinateDerivative i (M (a i j) u))) -
    ∑ i, scalarCoordinateDerivative i (M (b i) u)

def scalarAdjointDrift (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (j : Fin 4) : S :=
  (∑ i, D i (a i j)) + (∑ i, D i (a j i)) - b j

def scalarAdjointPotential (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) : S :=
  (∑ i, ∑ j, D j (D i (a i j))) - ∑ i, D i (b i)

theorem scalarAdjoint_second_product (a : S) (u : T) (i j : Fin 4) :
    scalarCoordinateDerivative j (scalarCoordinateDerivative i (M a u)) =
      M a (scalarCoordinateDerivative i (scalarCoordinateDerivative j u)) +
        M (D i a) (scalarCoordinateDerivative j u) +
        M (D j a) (scalarCoordinateDerivative i u) + M (D j (D i a)) u := by
  rw [scalarCoordinateDerivative_multiplier]
  change LineDeriv.lineDerivOpCLM ℂ T (EuclideanSpace.basisFun (Fin 4) ℝ j) (_ + _) = _
  rw [map_add]
  change scalarCoordinateDerivative j (M (D i a) u) +
    scalarCoordinateDerivative j (M a (scalarCoordinateDerivative i u)) = _
  rw [scalarCoordinateDerivative_multiplier, scalarCoordinateDerivative_multiplier,
    scalarCoordinateDerivative_commute j i]
  change M (D j (D i a)) u + M (D i a) (scalarCoordinateDerivative j u) +
    (M (D j a) (scalarCoordinateDerivative i u) +
      M a (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) = _
  abel

theorem scalarFormalAdjointOperator_expansion (a : Fin 4 → Fin 4 → S)
    (b : Fin 4 → S) (u : T) :
    scalarFormalAdjointOperator a b u =
      scalarPerturbedOperator a (scalarAdjointDrift a b) u +
        M (scalarAdjointPotential a b) u := by
  have hfirst : (∑ i, ∑ j, M (D i (a i j)) (scalarCoordinateDerivative j u)) =
      ∑ j, ∑ i, M (D i (a i j)) (scalarCoordinateDerivative j u) := Finset.sum_comm
  have hsecond : (∑ i, ∑ j, M (D j (a i j)) (scalarCoordinateDerivative i u)) =
      ∑ j, ∑ i, M (D i (a j i)) (scalarCoordinateDerivative j u) := by
    rfl
  unfold scalarFormalAdjointOperator
  simp_rw [scalarAdjoint_second_product]
  simp only [scalarCoordinateDerivative_multiplier, scalarPerturbedOperator,
    scalarAdjointDrift, scalarAdjointPotential, scalar_adjoint_multiplier_add,
    scalar_adjoint_multiplier_sub, scalar_adjoint_multiplier_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hfirst, hsecond]
  simp only [scalarSchwartzCoordinateDerivative]
  abel

theorem scalarAdjointDrift_bound (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (ha : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ) (j : Fin 4) (x : V) :
    ‖scalarAdjointDrift a b j x‖ ≤ 9 * δ := by
  simp only [scalarAdjointDrift, sub_apply, add_apply, sum_apply]
  exact scalar_adjoint_nine_bound _ _ _ δ (fun i => ha i j i x)
    (fun i => ha j i i x) (hb j x)

theorem scalarAdjointDrift_derivative_bound (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (δ : ℝ) (ha : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i k x, ‖D k (b i) x‖ ≤ δ) (j k : Fin 4) (x : V) :
    ‖D k (scalarAdjointDrift a b j) x‖ ≤ 9 * δ := by
  have hD : D k (scalarAdjointDrift a b j) =
      (∑ i, D k (D i (a i j))) + (∑ i, D k (D i (a j i))) - D k (b j) := by
    change (LineDeriv.lineDerivOpCLM ℂ S (EuclideanSpace.basisFun (Fin 4) ℝ k))
      ((∑ i, D i (a i j)) + (∑ i, D i (a j i)) - b j) = _
    rw [map_sub, map_add, map_sum, map_sum]
    rfl
  rw [hD]
  simp only [sub_apply, add_apply, sum_apply]
  exact scalar_adjoint_nine_bound _ _ _ δ (fun i => ha i j k i x)
    (fun i => ha j i k i x) (hb j k x)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarAdjointTests
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Test pairing for the adjoint operator arising from the actual
density-weighted chart equation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

def scalarSchwartzDirectOperator (a : Fin 4 → Fin 4 → S)
    (b : Fin 4 → S) (φ : S) : S :=
  scalarSchwartzHelmholtz φ +
    (∑ i, ∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) (D i (D j φ))) +
    ∑ i, SchwartzMap.smulLeftCLM ℂ (b i) (D i φ)

theorem scalarFormalAdjointOperator_pairing (a : Fin 4 → Fin 4 → S)
    (b : Fin 4 → S) (u : T) (φ : S) :
    scalarFormalAdjointOperator a b u φ = u (scalarSchwartzDirectOperator a b φ) := by
  simp only [scalarFormalAdjointOperator, scalarSchwartzDirectOperator,
    add_apply, sub_apply, sum_apply, scalarSchwartzHelmholtz_transpose,
    map_add, map_sum]
  simp only [scalarCoordinateDerivative, scalarSchwartzCoordinateDerivative,
    lineDerivOp_apply_apply, map_neg, smulLeftCLM_apply_apply]
  rw [Finset.sum_neg_distrib]
  abel_nf

theorem scalarFormalAdjointOperator_remainder (a : Fin 4 → Fin 4 → S)
    (b : Fin 4 → S) (u : T) :
    scalarPerturbedOperator a (scalarAdjointDrift a b) u - u -
        M (-scalarAdjointPotential a b : S) u =
      scalarFormalAdjointOperator a b u - u := by
  have hn : M (-scalarAdjointPotential a b : S) u = -M (scalarAdjointPotential a b) u := by
    change M (-(scalarAdjointPotential a b : V → ℂ)) u = _
    rw [smulLeftCLM_neg (scalarAdjointPotential a b).hasTemperateGrowth, neg_apply]
  rw [scalarFormalAdjointOperator_expansion, hn]
  abel

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelLocalization
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A variable-coefficient cutoff commutator loses only one derivative.
Nested cutoffs let this estimate use regularity on a larger neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_cutoff_second_product (ψ : S) (u : T) (i j : Fin 4) :
    scalarCoordinateDerivative i (scalarCoordinateDerivative j (M ψ u)) =
      M ψ (scalarCoordinateDerivative i (scalarCoordinateDerivative j u)) +
        M (D j ψ) (scalarCoordinateDerivative i u) +
        M (D i ψ) (scalarCoordinateDerivative j u) + M (D i (D j ψ)) u := by
  rw [scalarCoordinateDerivative_multiplier]
  change LineDeriv.lineDerivOpCLM ℂ T (EuclideanSpace.basisFun (Fin 4) ℝ i) (_ + _) = _
  rw [map_add]
  change scalarCoordinateDerivative i (M (D j ψ) u) +
    scalarCoordinateDerivative i (M ψ (scalarCoordinateDerivative j u)) = _
  rw [scalarCoordinateDerivative_multiplier, scalarCoordinateDerivative_multiplier]
  change M (D i (D j ψ)) u + M (D j ψ) (scalarCoordinateDerivative i u) +
    (M (D i ψ) (scalarCoordinateDerivative j u) +
      M ψ (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) = _
  abel

theorem scalar_cutoff_first_term (a ψ : S) (u : T) (i : Fin 4) :
    M a (scalarCoordinateDerivative i (M ψ u)) =
      M ψ (M a (scalarCoordinateDerivative i u)) + M a (M (D i ψ) u) := by
  rw [scalarCoordinateDerivative_multiplier]
  change M a (M (D i ψ) u + M ψ (scalarCoordinateDerivative i u)) = _
  rw [map_add, scalar_multiplier_commute a ψ]
  abel

theorem scalar_cutoff_second_term (a ψ : S) (u : T) (i j : Fin 4) :
    M a (scalarCoordinateDerivative i (scalarCoordinateDerivative j (M ψ u))) =
      M ψ (M a (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) +
        M a (M (D j ψ) (scalarCoordinateDerivative i u) +
          M (D i ψ) (scalarCoordinateDerivative j u) + M (D i (D j ψ)) u) := by
  rw [scalar_cutoff_second_product]
  simp only [map_add]
  rw [scalar_multiplier_commute a ψ]
  abel

/-- The commutator with a cutoff, for the actual differential operator. -/
def scalarPerturbedCutoffCommutator (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (ψ : S) (u : T) : T :=
  scalarPerturbedOperator a b (M ψ u) - M ψ (scalarPerturbedOperator a b u)

theorem scalarPerturbedCutoffCommutator_eq (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (ψ : S) (u : T) :
    scalarPerturbedCutoffCommutator a b ψ u =
      -(Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) • scalarLaplacianCommutator ψ u +
        (∑ i : Fin 4, ∑ j : Fin 4, M (a i j)
          (M (D j ψ) (scalarCoordinateDerivative i u) +
            M (D i ψ) (scalarCoordinateDerivative j u) + M (D i (D j ψ)) u)) +
        ∑ i : Fin 4, M (b i) (M (D i ψ) u) := by
  unfold scalarPerturbedCutoffCommutator scalarPerturbedOperator
  rw [scalar_cutoff_helmholtz]
  simp_rw [scalar_cutoff_second_term, scalar_cutoff_first_term]
  simp only [map_add, map_sum, Finset.sum_add_distrib]
  module

/-- The full variable-coefficient cutoff commutator has differential order one. -/
theorem scalarPerturbedCutoffCommutator_memSobolev
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (ψ : S) (n : ℕ) (u : T)
    (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 u) :
    MemSobolev (n : ℝ) 2 (scalarPerturbedCutoffCommutator a b ψ u) := by
  have hstep : MemSobolev (n : ℝ) 2 u ∧
      ∀ i : Fin 4, MemSobolev (n : ℝ) 2 (scalarCoordinateDerivative i u) := by
    apply (scalar_memSobolev_succ_iff (n : ℝ) u).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hu
  rw [scalarPerturbedCutoffCommutator_eq]
  apply MemSobolev.add
  · apply MemSobolev.add
    · exact (scalarLaplacianCommutator_memSobolev n ψ u hu).smul _
    · apply scalar_sobolev_sum_p1 n
      intro i
      apply scalar_sobolev_sum_p1 n
      intro j
      apply scalar_memSobolev_schwartz_multiplier n
      exact ((scalar_memSobolev_schwartz_multiplier n (D j ψ) _ (hstep.2 i)).add
        (scalar_memSobolev_schwartz_multiplier n (D i ψ) _ (hstep.2 j))).add
        (scalar_memSobolev_schwartz_multiplier n (D i (D j ψ)) _ hstep.1)
  · apply scalar_sobolev_sum_p1 n
    intro i
    exact scalar_memSobolev_schwartz_multiplier n (b i) _
      (scalar_memSobolev_schwartz_multiplier n (D i ψ) _ hstep.1)

theorem scalar_cutoff_nested_first_zero (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i : Fin 4) : (D i χ : V → ℂ) * ψ = 0 := by
  funext x
  by_cases hx : ψ x = 0
  · simp only [Pi.mul_apply, hx, mul_zero, Pi.zero_apply]
  · have hm : x ∈ tsupport (ψ : V → ℂ) := subset_closure hx
    have hd := (h x hm).fderiv_eq (𝕜 := ℝ)
    have hz : D i χ x = 0 := by
      change (fderiv ℝ (χ : V → ℂ) x) (EuclideanSpace.basisFun (Fin 4) ℝ i) = 0
      simp only [hd, fderiv_const_apply, zero_apply]
    simp only [Pi.mul_apply, hz, zero_mul, Pi.zero_apply]

theorem scalar_cutoff_nested_second_zero (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i j : Fin 4) : (D i (D j χ) : V → ℂ) * ψ = 0 := by
  funext x
  by_cases hx : ψ x = 0
  · simp only [Pi.mul_apply, hx, mul_zero, Pi.zero_apply]
  · have hm : x ∈ tsupport (ψ : V → ℂ) := subset_closure hx
    have hd : (D j χ : V → ℂ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(h x hm).fderiv (𝕜 := ℝ)] with y hy
      change (fderiv ℝ (χ : V → ℂ) y) (EuclideanSpace.basisFun (Fin 4) ℝ j) = 0
      simp only [hy, fderiv_const_apply, zero_apply]
    have hz : D i (D j χ) x = 0 := by
      change (fderiv ℝ (D j χ : V → ℂ) x) (EuclideanSpace.basisFun (Fin 4) ℝ i) = 0
      simp only [hd.fderiv_eq (𝕜 := ℝ), fderiv_const_apply, zero_apply]
    simp only [Pi.mul_apply, hz, zero_mul, Pi.zero_apply]

theorem scalar_cutoff_nested_first_mul (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i : Fin 4) (u : T) : M ψ (M (D i χ) u) = 0 := by
  rw [smulLeftCLM_smulLeftCLM_apply (D i χ).hasTemperateGrowth ψ.hasTemperateGrowth,
    scalar_cutoff_nested_first_zero ψ χ h i]
  exact (smulLeftCLM_const (F := ℂ) 0 u).trans (zero_smul ℂ u)

theorem scalar_cutoff_nested_second_mul (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i j : Fin 4) (u : T) : M ψ (M (D i (D j χ)) u) = 0 := by
  rw [smulLeftCLM_smulLeftCLM_apply (D i (D j χ)).hasTemperateGrowth ψ.hasTemperateGrowth,
    scalar_cutoff_nested_second_zero ψ χ h i j]
  exact (smulLeftCLM_const (F := ℂ) 0 u).trans (zero_smul ℂ u)

theorem scalar_cutoff_nested_derivative (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i : Fin 4) (u : T) :
    M ψ (scalarCoordinateDerivative i (M χ u)) = M ψ (scalarCoordinateDerivative i u) := by
  rw [scalarCoordinateDerivative_multiplier, map_add]
  change M ψ (M (D i χ) u) + M ψ (M χ (scalarCoordinateDerivative i u)) = _
  rw [scalar_cutoff_nested_first_mul ψ χ h, scalar_cutoff_nested_mul ψ χ h, zero_add]

theorem scalar_cutoff_nested_second_derivative (ψ χ : S) (h : ScalarCutoffNested ψ χ)
    (i j : Fin 4) (u : T) :
    M ψ (scalarCoordinateDerivative i (scalarCoordinateDerivative j (M χ u))) =
      M ψ (scalarCoordinateDerivative i (scalarCoordinateDerivative j u)) := by
  rw [scalar_cutoff_second_product]
  simp only [map_add]
  rw [scalar_cutoff_nested_mul ψ χ h, scalar_cutoff_nested_first_mul ψ χ h,
    scalar_cutoff_nested_first_mul ψ χ h, scalar_cutoff_nested_second_mul ψ χ h]
  simp only [add_zero]

/-- Inner localization of the equation is unchanged by inserting an outer cutoff. -/
theorem scalarPerturbedOperator_nested_cutoff (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (ψ χ : S) (h : ScalarCutoffNested ψ χ) (u : T) :
    M ψ (scalarPerturbedOperator a b (M χ u)) = M ψ (scalarPerturbedOperator a b u) := by
  have hΔ : M ψ (Δ (M χ u)) = M ψ (Δ u) := by
    rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ),
      TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ)]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact scalar_cutoff_nested_second_derivative ψ χ h i i u
  have hH : M ψ (normalizedScalarHelmholtz (M χ u)) = M ψ (normalizedScalarHelmholtz u) := by
    simp only [normalizedScalarHelmholtz, map_sub, scalar_multiplier_real_smul]
    rw [scalar_cutoff_nested_mul ψ χ h, hΔ]
  have hsecond (i j : Fin 4) :
      M ψ (M (a i j) (scalarCoordinateDerivative i (scalarCoordinateDerivative j (M χ u)))) =
        M ψ (M (a i j) (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) := by
    rw [scalar_multiplier_commute ψ (a i j), scalar_multiplier_commute ψ (a i j),
      scalar_cutoff_nested_second_derivative ψ χ h]
  have hfirst (i : Fin 4) :
      M ψ (M (b i) (scalarCoordinateDerivative i (M χ u))) =
        M ψ (M (b i) (scalarCoordinateDerivative i u)) := by
    rw [scalar_multiplier_commute ψ (b i), scalar_multiplier_commute ψ (b i),
      scalar_cutoff_nested_derivative ψ χ h]
  simp only [scalarPerturbedOperator, map_add, map_sum, hH, hsecond, hfirst]

/-- One nested-cutoff step gains one local Sobolev order. -/
theorem scalar_nested_cutoff_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (ψ χ : S) (hnest : ScalarCutoffNested ψ χ) (n : ℕ) (u : T)
    (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M χ u))
    (hf : MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u))) :
    MemSobolev ((n + 2 : ℕ) : ℝ) 2 (M ψ u) := by
  have hzero : MemSobolev 0 2 (M ψ u) := by
    rw [← scalar_cutoff_nested_mul ψ χ hnest]
    exact (scalar_memSobolev_schwartz_multiplier (n + 1) ψ _ hu).mono (by positivity)
  have heq : scalarPerturbedOperator a b (M ψ u) =
      M ψ (scalarPerturbedOperator a b u) + scalarPerturbedCutoffCommutator a b ψ (M χ u) := by
    rw [scalarPerturbedCutoffCommutator,
      scalar_cutoff_nested_mul ψ χ hnest, scalarPerturbedOperator_nested_cutoff a b ψ χ hnest]
    abel
  exact scalar_small_elliptic_integer_regularity a b δ hδ ha ha1 ha2 hb hb1 hsmall n
    (M ψ u) _ hzero
    (hf.add (scalarPerturbedCutoffCommutator_memSobolev a b ψ n (M χ u) hu)) heq

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelSobolev
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily high scalar Sobolev regularity produces a smooth function.
The representative is constructed by inverse Fourier integration, rather than
assumed as an elliptic regularity input. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BoundedContinuousFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sobolevReciprocal_temperate (n : ℕ) :
    (sobolevReciprocal (E := E) n).HasTemperateGrowth := by
  unfold sobolevReciprocal
  fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sobolevReciprocal_norm (n : ℕ) (x : E) :
    ‖sobolevReciprocal n x‖ = ((1 + ‖x‖ ^ 2) ^ n)⁻¹ := by
  rw [sobolevReciprocal, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (Real.rpow_pos_of_pos (show 0 < 1 + ‖x‖ ^ 2 by positivity) _)]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem sobolevReciprocal_memLp (n : ℕ) :
    MemLp (sobolevReciprocal (E := E) n) ∞ (volume : Measure E) := by
  let f : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (sobolevReciprocal n) (sobolevReciprocal_temperate n).1.continuous 1 (by
      intro x
      rw [sobolevReciprocal_norm]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith [sq_nonneg ‖x‖])))
  exact f.memLp_top

/-- Every polynomial moment of the Fourier representative is integrable. -/
theorem scalar_sobolev_fourier_moments (u : 𝓢'(E, ℂ))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 u)
    (v : Lp ℂ 1 (volume : Measure E)) (hv : 𝓕 u = (v : 𝓢'(E, ℂ)))
    (n : ℕ) : Integrable (fun x : E => ‖x‖ ^ n * ‖v x‖) := by
  obtain ⟨w, hw⟩ := scalar_fourier_weight_memL1 u hu n
  let hρ := sobolevReciprocal_memLp (E := E) n
  let v' : Lp ℂ 1 (volume : Measure E) := hρ.toLp • w
  have heq : (v' : 𝓢'(E, ℂ)) = v := by
    dsimp [v']
    rw [Lp.toTemperedDistribution_smul_eq (sobolevReciprocal_temperate n),
      ← hw, smulLeftCLM_smulLeftCLM_apply (by fun_prop)
        (sobolevReciprocal_temperate n)]
    have hm : (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ n)) *
        sobolevReciprocal n = fun _ : E => (1 : ℂ) := by
      ext x
      simp only [Pi.mul_apply, sobolevReciprocal]
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← Complex.ofReal_mul]
      simp [ne_of_gt (show 0 < (1 + ‖x‖ ^ 2) ^ n by positivity)]
    rw [hm, smulLeftCLM_const, one_smul, hv]
  have hv' : v' = v :=
    (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure E)))) heq
  have hpoint : ∀ᵐ x ∂(volume : Measure E),
      v x = sobolevReciprocal n x * w x := by
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (hρ.toLp) w,
      hρ.coeFn_toLp] with x hx hρx
    rw [← hv']
    exact hx.trans (by simp only [smul_eq_mul, Pi.mul_apply, hρx])
  have hmeas : AEStronglyMeasurable (fun x : E => ‖x‖ ^ n * ‖v x‖)
      (volume : Measure E) :=
    ((continuous_norm.pow n).aestronglyMeasurable).mul (Lp.aestronglyMeasurable v).norm
  refine ((memLp_one_iff_integrable.mp (Lp.memLp w)).norm).mono' hmeas ?_
  filter_upwards [hpoint] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hx, norm_mul, ← mul_assoc]
  have hb : 0 < (1 + ‖x‖ ^ 2) ^ n := by positivity
  have hp : ‖x‖ ^ n ≤ (1 + ‖x‖ ^ 2) ^ n := by
    gcongr
    nlinarith [sq_nonneg (‖x‖ - 1)]
  have hc : ‖x‖ ^ n * ‖sobolevReciprocal n x‖ ≤ 1 := by
    rw [sobolevReciprocal_norm]
    simpa only [mul_inv_cancel₀ hb.ne'] using
      mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr hb.le)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (w x))

/-- Arbitrarily high L2 Sobolev regularity gives an actual smooth representative,
with equality against every Schwartz test function. -/
theorem scalar_sobolev_smooth_representative (u : 𝓢'(E, ℂ))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 u) :
    ∃ f : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ φ : 𝓢(E, ℂ), u φ = ∫ x : E, φ x * f x := by
  obtain ⟨v, hv⟩ := scalar_fourier_weight_memL1 u hu 0
  simp only [pow_zero, Complex.ofReal_one, smulLeftCLM_const, one_smul] at hv
  refine ⟨𝓕⁻ (v : E → ℂ), ?_, ?_⟩
  · have hf : ContDiff ℝ (⊤ : ℕ∞) (𝓕 (v : E → ℂ)) :=
      Real.contDiff_fourier (fun n _ => scalar_sobolev_fourier_moments u hu v hv n)
    have he : (𝓕⁻ (v : E → ℂ)) = (fun x : E => (𝓕 (v : E → ℂ)) (-x)) := by
      funext x
      exact Real.fourierInv_eq_fourier_neg _ _
    rw [he]
    exact hf.comp (contDiff_id.neg)
  · intro φ
    calc
      u φ = (𝓕⁻ (v : 𝓢'(E, ℂ))) φ := by rw [← hv, fourierInv_fourier_eq]
      _ = _ := inverse_fourier_pairing v φ

/-- For an L2 function, the constructed smooth function agrees almost everywhere
with the original representative. -/
theorem scalar_L2_sobolev_smooth_representative (u : Lp ℂ 2 (volume : Measure E))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (u : 𝓢'(E, ℂ))) :
    ∃ f : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (u : E → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, hf, heq⟩ := scalar_sobolev_smooth_representative (u : 𝓢'(E, ℂ)) hu
  refine ⟨f, hf, ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num)) hf.continuous.locallyIntegrable ?_⟩
  intro ψ hψ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hs' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have h := heq (hc'.toSchwartzMap hs')
  rw [Lp.toTemperedDistribution_apply] at h
  change (∫ x : E, (ψ x : ℂ) * u x) = ∫ x : E, (ψ x : ℂ) * f x at h
  simpa only [Complex.real_smul, smul_eq_mul] using h

/-- The real part inherits a smooth representative without requiring a
complex-valued formulation from a geometric caller. -/
theorem scalar_L2_sobolev_smooth_real_representative
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (u : 𝓢'(E, ℂ))) :
    ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (fun x : E => (u x).re) =ᵐ[volume] f := by
  obtain ⟨f, hf, heq⟩ := scalar_L2_sobolev_smooth_representative u hu
  refine ⟨Complex.reCLM ∘ f, Complex.reCLM.contDiff.comp hf, ?_⟩
  filter_upwards [heq] with x hx
  change (u x).re = (f x).re
  rw [hx]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelCutoffs
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete nested compact cutoffs inside the unit ball. Their radii tend
to one, while each support lies strictly inside the next region of value one. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)

theorem scalarBumpGap_pos {r : ℝ} (hr : r < 1) (k : ℕ) :
    0 < scalarBumpGap r k := by
  exact mul_pos (sub_pos.mpr hr) (pow_pos (by norm_num) _)

theorem scalarBumpGap_lt {r : ℝ} (hr : r < 1) (k : ℕ) :
    scalarBumpGap r k < 1 - r := by
  have hp : (1 / 4 : ℝ) ^ (k + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero k)
  simpa only [scalarBumpGap, mul_one] using
    mul_lt_mul_of_pos_left hp (sub_pos.mpr hr)

theorem scalarBumpGap_succ (r : ℝ) (k : ℕ) :
    scalarBumpGap r (k + 1) = scalarBumpGap r k / 4 := by
  simp only [scalarBumpGap, pow_succ]
  ring

/-- A concrete real bump; the gap shrinks geometrically with the index. -/
def scalarNestedRealBump (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    ContDiffBump (0 : V) where
  rIn := 1 - scalarBumpGap r k
  rOut := 1 - scalarBumpGap r k / 2
  rIn_pos := by
    have hg := scalarBumpGap_lt hr1 k
    linarith
  rIn_lt_rOut := by
    have hg := scalarBumpGap_pos hr1 k
    linarith

theorem scalarNestedRealBump_inner {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    r < (scalarNestedRealBump r hr0 hr1 k).rIn := by
  change r < 1 - scalarBumpGap r k
  linarith [scalarBumpGap_lt hr1 k]

theorem scalarNestedRealBump_outer {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (scalarNestedRealBump r hr0 hr1 k).rOut < 1 := by
  change 1 - scalarBumpGap r k / 2 < 1
  linarith [scalarBumpGap_pos hr1 k]

theorem scalarNestedRealBump_separated {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (scalarNestedRealBump r hr0 hr1 k).rOut <
      (scalarNestedRealBump r hr0 hr1 (k + 1)).rIn := by
  change 1 - scalarBumpGap r k / 2 < 1 - scalarBumpGap r (k + 1)
  rw [scalarBumpGap_succ]
  linarith [scalarBumpGap_pos hr1 k]

/-- Complexification turns the actual compact real bump into a Schwartz cutoff. -/
def scalarNestedBumpSchwartz (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) : S :=
  ((scalarNestedRealBump r hr0 hr1 k).hasCompactSupport.comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (scalarNestedRealBump r hr0 hr1 k).contDiff)

theorem scalarNestedBumpSchwartz_apply (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℕ) (x : V) :
    scalarNestedBumpSchwartz r hr0 hr1 k x = (scalarNestedRealBump r hr0 hr1 k x : ℂ) := rfl

theorem scalarNestedBumpSchwartz_tsupport (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) :
    tsupport (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =
      closedBall 0 (scalarNestedRealBump r hr0 hr1 k).rOut := by
  have hs : Function.support (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =
      Function.support (scalarNestedRealBump r hr0 hr1 k : V → ℝ) := by
    ext x
    simp only [Function.mem_support, scalarNestedBumpSchwartz_apply, ne_eq,
      Complex.ofReal_eq_zero]
  rw [tsupport, hs]
  exact (scalarNestedRealBump r hr0 hr1 k).tsupport_eq

theorem scalarNestedBumpSchwartz_one_nhds (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) {x : V}
    (hx : x ∈ ball 0 (scalarNestedRealBump r hr0 hr1 k).rIn) :
    (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [(scalarNestedRealBump r hr0 hr1 k).eventuallyEq_one_of_mem_ball hx] with y hy
  simp only [scalarNestedBumpSchwartz_apply, hy, Pi.one_apply, Complex.ofReal_one]

theorem scalarNestedBumpSchwartz_nested (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) :
    ScalarCutoffNested (scalarNestedBumpSchwartz r hr0 hr1 k)
      (scalarNestedBumpSchwartz r hr0 hr1 (k + 1)) := by
  intro x hx
  rw [scalarNestedBumpSchwartz_tsupport] at hx
  apply scalarNestedBumpSchwartz_one_nhds
  exact (mem_closedBall.mp hx).trans_lt (scalarNestedRealBump_separated hr0 hr1 k)

/-- Every compact cutoff inside a smaller closed ball starts a concrete
infinite nested sequence supported in the open unit ball. -/
theorem exists_scalar_nested_cutoffs (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
    (hφ : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    ∃ ψ : ℕ → S, ψ 0 = φ ∧ (∀ k, ScalarCutoffNested (ψ k) (ψ (k + 1))) ∧
      ∀ k, HasCompactSupport (ψ k : V → ℂ) ∧ tsupport (ψ k : V → ℂ) ⊆ ball 0 1 := by
  let ψ : ℕ → S := fun k => match k with
    | 0 => φ
    | j + 1 => scalarNestedBumpSchwartz r hr0 hr1 j
  refine ⟨ψ, rfl, ?_, ?_⟩
  · intro k
    cases k with
    | zero =>
        intro x hx
        apply scalarNestedBumpSchwartz_one_nhds
        exact (mem_closedBall.mp (hφ hx)).trans_lt (scalarNestedRealBump_inner hr0 hr1 0)
    | succ k => exact scalarNestedBumpSchwartz_nested r hr0 hr1 k
  · intro k
    cases k with
    | zero =>
        refine ⟨hφc, ?_⟩
        intro x hx
        exact (mem_closedBall.mp (hφ hx)).trans_lt hr1
    | succ k =>
        change HasCompactSupport (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ) ∧ _
        constructor
        · change IsCompact (tsupport (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ))
          rw [scalarNestedBumpSchwartz_tsupport]
          exact isCompact_closedBall _ _
        · intro x hx
          rw [scalarNestedBumpSchwartz_tsupport] at hx
          exact (mem_closedBall.mp hx).trans_lt (scalarNestedRealBump_outer hr0 hr1 k)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelLocalRepresentative
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local smooth representatives of the original L2 function. The cutoff
is one on a smaller ball, so Fourier regularization returns the given
solution there, not just a solution of a related equation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

/-- All Sobolev orders for an inner localization give a smooth function
agreeing with the original L2 function wherever the cutoff is one. -/
theorem scalar_L2_cutoff_smooth_on (u : L2) (φ : S) (B : Set V)
    (hB : MeasurableSet B) (hone : ∀ x ∈ B, φ x = 1)
    (hreg : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M φ (u : T))) :
    ∃ f : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (u : V → ℂ) =ᵐ[volume.restrict B] f := by
  have hv : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (scalarCutoffL2 φ u : T) := by
    intro n
    rw [scalarCutoffL2_distribution]
    exact hreg n
  obtain ⟨f, hf, heq⟩ := scalar_L2_sobolev_smooth_representative (scalarCutoffL2 φ u) hv
  refine ⟨f, hf, ?_⟩
  change ∀ᵐ x ∂volume.restrict B, u x = f x
  rw [ae_restrict_iff' hB]
  filter_upwards [heq, scalarCutoffL2_ae φ u] with x hx hprod
  intro hxB
  calc
    u x = φ x * u x := by rw [hone x hxB, one_mul]
    _ = scalarCutoffL2 φ u x := hprod.symm
    _ = f x := hx

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelPotential
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth zeroth-order potential does not obstruct the local bootstrap.
Only the principal and first-order perturbations need to be small. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

variable (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
  (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
  (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
  (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
  (hb : ∀ i x, ‖b i x‖ ≤ δ)
  (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
  (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)

include hδ ha ha1 ha2 hb hb1 hsmall

/-- The potential times u has the needed order from the outer cutoff; it
is not required to be smooth before the bootstrap. -/
theorem scalar_nested_cutoff_gain_of_potential (c ψ χ : S)
    (hnest : ScalarCutoffNested ψ χ) (n : ℕ) (u : T)
    (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M χ u))
    (hf : MemSobolev (n : ℝ) 2
      (M ψ (scalarPerturbedOperator a b u - u - M c u))) :
    MemSobolev ((n + 2 : ℕ) : ℝ) 2 (M ψ u) := by
  have hi : MemSobolev (n : ℝ) 2 (M ψ u) := by
    rw [← scalarCutoffNested_mul ψ χ hnest]
    exact (scalar_memSobolev_schwartz_multiplier (n + 1) ψ _ hu).mono
      (by exact_mod_cast Nat.le_succ n)
  have hp : MemSobolev (n : ℝ) 2 (M c (M ψ u)) :=
    scalar_memSobolev_schwartz_multiplier n c _ hi
  have heq : M ψ (scalarPerturbedOperator a b u) =
      M ψ u + M c (M ψ u) +
        M ψ (scalarPerturbedOperator a b u - u - M c u) := by
    rw [map_sub, map_sub, scalarPotential_multipliers_commute]
    abel
  have hsource : MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u)) := by
    rw [heq]
    exact (hi.add hp).add hf
  exact scalar_nested_cutoff_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall ψ χ hnest n u hu hsource

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarFullBallIntegerGain
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nested-cutoff estimate gains two derivatives from an
integer-order source. This is the finite-order bootstrap used for the
linear harmonic two-form equation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

variable (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
  (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
  (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
  (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
  (hb : ∀ i x, ‖b i x‖ ≤ δ)
  (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
  (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)

include hδ ha ha1 ha2 hb hb1 hsmall in
theorem scalar_finite_cutoff_chain_source_gain (c : S) (u : T)
    (n : ℕ) (ψ : ℕ → S)
    (hnest : ∀ k < n, ScalarCutoffNested (ψ k) (ψ (k + 1)))
    (hu : MemSobolev 1 2 (M (ψ n) u))
    (hf : ∀ k ≤ n, MemSobolev ((n : ℝ) - 1) 2
      (M (ψ k) (scalarPerturbedOperator a b u - u - M c u))) :
    MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 0) u) := by
  induction n generalizing ψ with
  | zero => simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using hu
  | succ n ih =>
      have ht : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 1) u) := by
        apply ih (fun k => ψ (k + 1))
        · intro k hk
          exact hnest (k + 1) (Nat.succ_lt_succ hk)
        · simpa only [Nat.succ_eq_add_one] using hu
        · intro k hk
          exact (hf (k + 1) (Nat.succ_le_succ hk)).mono (by
            rw [Nat.cast_succ]
            linarith)
      have hs : MemSobolev (n : ℝ) 2
          (M (ψ 0) (scalarPerturbedOperator a b u - u - M c u)) := by
        simpa only [Nat.cast_succ, add_sub_cancel_right] using hf 0 (Nat.zero_le _)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
          c (ψ 0) (ψ 1) (hnest 0 (Nat.zero_lt_succ n)) n u ht hs

include hδ ha ha1 ha2 hb hb1 hsmall in
theorem scalar_ball_integer_forcing_gain (n : ℕ) (c : S) (u f : T)
    (hf : MemSobolev (n : ℝ) 2 f) (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = f ψ)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    MemSobolev ((n + 2 : ℕ) : ℝ) 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hc hs
  have hsource (k : ℕ) : MemSobolev (n : ℝ) 2
      (M (ψ k) (scalarPerturbedOperator a b u - u - M c u)) := by
    rw [scalar_localize_eq_of_tests (ball 0 1) _ f htest (ψ k) (hsupp k).1 (hsupp k).2]
    exact scalar_memSobolev_schwartz_multiplier n (ψ k) f hf
  have houter : MemSobolev 1 2 (M (ψ (n + 1)) u) := by
    simpa only [Nat.cast_one] using scalar_memSobolev_schwartz_multiplier 1 (ψ (n + 1)) u
      (by simpa only [Nat.cast_one] using hu)
  have hg := scalar_finite_cutoff_chain_source_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
    c u (n + 1) ψ (fun k _ => hnest k) houter (fun k _ => by
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hsource k)
  simpa only [Nat.add_assoc, Nat.reduceAdd, hψ] using hg

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarHomogeneousInteger
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A homogeneous scalar elliptic equation has all local integer Sobolev
orders. The zeroth-order coefficient includes the eigenvalue. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_homogeneous_all_integer_orders
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (u : T) (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = 0)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ n : ℕ, ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 r →
      MemSobolev (n : ℝ) 2 (M φ u) := by
  intro n φ hc hs
  have hg := scalar_ball_integer_forcing_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
    n c u 0 (memSobolev_fun_zero V ℂ (n : ℝ) 2) hu htest r hr0 hr1 φ hc hs
  exact hg.mono (by push_cast; linarith)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarEigenMultiplier
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorbing the actual scalar eigenvalue into a compact zeroth-order
coefficient, on the ball where the equation is tested. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_eigen_all_integer_orders
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c θ : S) (κ : ℂ) (hθ : ∀ x ∈ ball (0 : V) 1, θ x = κ)
    (u : T) (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = κ * u ψ)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ n : ℕ, ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 r →
      MemSobolev (n : ℝ) 2 (M φ u) := by
  apply scalar_homogeneous_all_integer_orders a b δ hδ ha ha1 ha2 hb hb1 hsmall
    (c + θ) u hu _ r hr0 hr1
  intro ψ hc hs
  have he := htest ψ hc hs
  rw [scalar_multiplier_add]
  simp only [sub_apply, add_apply] at he ⊢
  rw [scalar_multiplier_constant_on_test θ ψ u κ (fun x hx => hθ x (hs hx))]
  linear_combination he

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Integer-order Bessel inverses on the actual Euclidean L2 space.
These supply the common smooth approximation for the higher nonlinear bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℂ)

def scalarIntegerBesselInverse (n : ℕ) : L2 →L[ℂ] L2 :=
  scalarL2FourierMultiplier ((integerBesselSymbol_memLp n).toLp _)

theorem scalarIntegerBesselInverse_distribution (n : ℕ) (f : L2) :
    (scalarIntegerBesselInverse n f : T) = besselPotential V ℂ (-(n : ℝ)) (f : T) := by
  rw [scalarIntegerBesselInverse, scalarL2FourierMultiplier_distribution _
    (integerBesselSymbol_temperate n) (integerBesselSymbol_memLp n), besselPotential]
  have hs : integerBesselSymbol n =
      fun x : V => (((1 + ‖x‖ ^ 2) ^ ((-(n : ℝ)) / 2) : ℝ) : ℂ) := by
    funext x
    simp only [integerBesselSymbol, neg_div]
  rw [hs]

theorem scalarIntegerBesselInverse_memSobolev (n : ℕ) (f : L2) :
    MemSobolev (n : ℝ) 2 (scalarIntegerBesselInverse n f : T) := by
  rw [scalarIntegerBesselInverse_distribution, memSobolev_besselPotential_iff, neg_add_cancel]
  exact memSobolev_zero_iff.mpr ⟨f, rfl⟩

theorem scalarSchwartzIntegerBesselInverse_toLp (n : ℕ) (φ : S) :
    (scalarSchwartzIntegerBesselInverse n φ).toLp 2 volume =
      scalarIntegerBesselInverse n (φ.toLp 2 volume) := by
  apply scalarL2_distribution_injective
  change ((scalarSchwartzIntegerBesselInverse n φ).toLp 2 volume : T) =
    (scalarIntegerBesselInverse n (φ.toLp 2 volume) : T)
  rw [Lp.toTemperedDistribution_toLp_eq, scalarSchwartzIntegerBesselInverse_distribution,
    scalarIntegerBesselInverse_distribution, Lp.toTemperedDistribution_toLp_eq]

theorem scalar_integer_Hn_schwartz_approximation (n : ℕ) (u : L2)
    (hu : MemSobolev (n : ℝ) 2 (u : T)) :
    ∃ v : L2, ∃ φ : ℕ → S,
      u = scalarIntegerBesselInverse n v ∧
      Tendsto (fun k => (φ k).toLp 2 volume) atTop (𝓝 v) ∧
      Tendsto (fun k => (scalarSchwartzIntegerBesselInverse n (φ k)).toLp 2 volume)
        atTop (𝓝 u) := by
  obtain ⟨v, hv⟩ := hu
  have heq : u = scalarIntegerBesselInverse n v := by
    apply scalarL2_distribution_injective
    change (u : T) = (scalarIntegerBesselInverse n v : T)
    rw [scalarIntegerBesselInverse_distribution, ← hv, besselPotential_besselPotential_apply]
    simp
  obtain ⟨vs, hvs, ht⟩ := mem_closure_iff_seq_limit.mp
    (SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ)
      (μ := (volume : Measure V)) (p := 2) (by norm_num) v)
  choose φ hφ using hvs
  have hφv : Tendsto (fun k => (φ k).toLp 2 volume) atTop (𝓝 v) := by
    have he : (fun k => (φ k).toLp 2 volume) = vs := funext (fun k => hφ k)
    rwa [he]
  refine ⟨v, φ, heq, hφv, ?_⟩
  simp only [scalarSchwartzIntegerBesselInverse_toLp, heq]
  exact (scalarIntegerBesselInverse n).continuous.continuousAt.tendsto.comp hφv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong L2 control of the finite coordinate jets of the Bessel inverse.
All derivatives are the actual distributional derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter LineDeriv
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

theorem besselJet_exists (n : ℕ) (is : List (Fin 4))
    (hle : is.length ≤ n) (f : L2) :
    ∃ v : L2, scalarCoordinateJet is (scalarIntegerBesselInverse n f : T) = (v : T) := by
  apply memSobolev_zero_iff.mp
  exact (scalarCoordinateJet_memSobolev is (scalarIntegerBesselInverse_memSobolev n f)).mono
    (sub_nonneg.mpr (by exact_mod_cast hle))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Lp representatives and convergence in the subcritical range.
The inclusion uses the same almost-everywhere function; the convergence
statement combines small L² norm with a bounded L⁴ norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

local instance instFactLeENNRealOfNat_solutions_13 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite signed Gram expansion of the four transport amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

def heatSignedGram (A B : HeatMat6) : ℝ :=
  (twoFormHodgeMatrix * (Aᵀ * B)).trace

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


