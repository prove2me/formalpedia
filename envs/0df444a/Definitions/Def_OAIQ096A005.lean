-- Prove2me | Definitions.Def_OAIQ096A005
-- name    : OAIQ096A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:32:49.317096+00:00
-- url     : https://prove2.me/theorems/61faa65a-8adb-4fca-ace2-330f68360251
-- title:
--   Definitions bundle OAIQ096A005 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 227 declarations of OpenAI's Lean: 93 definitions, 2 instances and 132 theorems. The definitions and types are `OAI.CubicFirstMoment.HeckeFunctionalEquation`, `OAI.CubicFirstMoment.InnerCubeIndex`, `OAI.CubicFirstMoment.LocalSobolev.Supported`, `OAI.CubicFirstMoment.LocalSobolev.complexInclusion`, `OAI.CubicFirstMoment.LocalSobolev.imagSupported`, `OAI.CubicFirstMoment.LocalSobolev.realSupported`, `OAI.CubicFirstMoment.LocalSobolev.realSupportedInclusion`, `OAI.CubicFirstMoment.LogarithmicWeightFamily.logPower`, `OAI.CubicFirstMoment.LogarithmicWeightFamily.normalize`, `OAI.CubicFirstMoment.LogarithmicWeightFamily.phase`, `OAI.CubicFirstMoment.MixedCubicNonprincipal`, `OAI.CubicFirstMoment.PrimaryArgument`, `OAI.CubicFirstMoment.ShiftedCompletedHeckeFiniteOrder`, `OAI.CubicFirstMoment.SieveExponent`, `OAI.CubicFirstMoment.UniformLogWeights.compactMultiplier`, `OAI.CubicFirstMoment.UniformLogWeights.finiteCoordinates`, `OAI.CubicFirstMoment.UniformLogWeights.logDilate`, `OAI.CubicFirstMoment.UniformLogWeights.logarithmicWithLength`, `OAI.CubicFirstMoment.UniformLogWeights.realPower`, `OAI.CubicFirstMoment.UniformLogWeights.reindex`, `OAI.CubicFirstMoment.allLogNormCells`, `OAI.CubicFirstMoment.angularFiniteHeckeDual`, `OAI.CubicFirstMoment.collectedSquarefreeSieveCoefficient`, `OAI.CubicFirstMoment.commonBlockCoefficient`, `OAI.CubicFirstMoment.commonBlockCost`, `OAI.CubicFirstMoment.commonBlockEnergy`, `OAI.CubicFirstMoment.commonOuterCost`, `OAI.CubicFirstMoment.commonRowFactors`, `OAI.CubicFirstMoment.compactDistinguishedSmoothWeights`, `OAI.CubicFirstMoment.conjugateFrequencyGauss`, `OAI.CubicFirstMoment.coprimeGramForm`, `OAI.CubicFirstMoment.coprimeNormMajorant`, `OAI.CubicFirstMoment.coprimeRadialForm`, `OAI.CubicFirstMoment.correctedDispersionPolynomial`, `OAI.CubicFirstMoment.cubeBlockMass`, `OAI.CubicFirstMoment.cubeBlockSupport`, `OAI.CubicFirstMoment.cubeFrequencyCover`, `OAI.CubicFirstMoment.cubeProfileIntegral`, `OAI.CubicFirstMoment.cubicThetaAxisFirst`, `OAI.CubicFirstMoment.cubicThetaAxisVector` and 53 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1`, `Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2`, `CubicGram_CommonRows`, `CubicGram_Conjugation`, `CubicGram_CubeEstimates`, `CubicGram_CubeExtraction`, `CubicGram_CubicOperator`, `CubicGram_DyadicRecurrence`, `CubicGram_EuclideanDomain`, `CubicGram_FrequencyGauss`, `CubicGram_FullCubeExtraction`, `CubicGram_GlobalRecurrence`, `CubicGram_GramPoisson`, `CubicGram_InnerExtension`, `CubicGram_LatticeCounts`, `CubicGram_LatticePoisson`, `CubicGram_MellinDecay`, `CubicGram_MellinNorm`, `CubicGram_MixedPoisson`, `CubicGram_Mobius`, `CubicGram_PeriodicPoisson`, `CubicGram_PrimaryNormalization`, `CubicGram_PrimeFactors`, `CubicGram_Reciprocity`, `CubicGram_SieveExponent`, `CubicGram_SquarefreeGauss`, `CubicMoment_Angular_AngularDualContour`, `CubicMoment_Angular_AngularHeckeGrowth`, `CubicMoment_Angular_AngularPowerWeights`, `CubicMoment_Angular_AngularWeightOperator`, `CubicMoment_Decomposition_PrimeProductEnvelope`, `CubicMoment_Estimates_CommonOuterBound`, `CubicMoment_Estimates_CompactParameterWeights`, `CubicMoment_Estimates_CubeAsymptotic`, `CubicMoment_Estimates_DispersionAlgebra`, `CubicMoment_Estimates_DispersionExpansion`, `CubicMoment_Estimates_FarLogNormCells`, `CubicMoment_Estimates_GaussianSchwartz`, `CubicMoment_Estimates_GaussianTrace`, `CubicMoment_Estimates_HeckeFunctionalEquation`, `CubicMoment_Estimates_IdealMoebiusBounds`, `CubicMoment_Estimates_LargeTupleWeights`, `CubicMoment_Estimates_LogNormCells`, `CubicMoment_Estimates_LogarithmicPhase`, `CubicMoment_Estimates_LogarithmicWeightFamily`, `CubicMoment_Estimates_MellinWeightFamily`, `CubicMoment_Estimates_NormSeries`, `CubicMoment_Estimates_PrimaryPrimePNTProofSplitting`, `CubicMoment_Estimates_PublishedHecke`, `CubicMoment_Estimates_RepeatedPrimeSupport`, `CubicMoment_Estimates_SparseEnvelopeWeights`, `CubicMoment_Estimates_SquarefreeJoin`, `CubicMoment_Estimates_StructuredConvolution`, `CubicMoment_Estimates_TypeILogCoefficients`, `CubicMoment_Estimates_TypeIMixedWeights`, `CubicMoment_Estimates_UniformWeightCoordinates`, `CubicMoment_Estimates_UniformWeightMultiplier`, `CubicMoment_Estimates_WideGramMellin`, `CubicMoment_Theta_CubicThetaArithmeticCuspEnergy`, `CubicMoment_Theta_CubicThetaAxisDifferentials`, `CubicMoment_Theta_CubicThetaChartSections`, `CubicMoment_Theta_CubicThetaCompactHeight`, `CubicMoment_Theta_CubicThetaCoordinateEnergyBound`, `CubicMoment_Theta_CubicThetaCoordinateIntegrability`, `CubicMoment_Theta_CubicThetaCoordinateIntegral`, `CubicMoment_Theta_CubicThetaCoordinateJets`, `CubicMoment_Theta_CubicThetaCoordinateSection`, `CubicMoment_Theta_CubicThetaCoordinateSectionSupport`, `CubicMoment_Theta_CubicThetaCuspStrip`, `CubicMoment_Theta_CubicThetaCuspVerticalEnergy`, `CubicMoment_Theta_CubicThetaCutoffEnergy`, `CubicMoment_Theta_CubicThetaEisensteinBounds`, `CubicMoment_Theta_CubicThetaFiniteEnergySum`, `CubicMoment_Theta_CubicThetaForcingProfile`, `CubicMoment_Theta_CubicThetaFunctionEnergyTransport`, `CubicMoment_Theta_CubicThetaGlobalLocalizationBound`, `CubicMoment_Theta_CubicThetaGridAnalytic`, `CubicMoment_Theta_CubicThetaGridJets`, `CubicMoment_Theta_CubicThetaHermitianMetric`, `CubicMoment_Theta_CubicThetaHorizontalSection`, `CubicMoment_Theta_CubicThetaHyperbolicIntegral`, `CubicMoment_Theta_CubicThetaHyperbolicMeasure`, `CubicMoment_Theta_CubicThetaJacobian`, `CubicMoment_Theta_CubicThetaL2Dominated`, `CubicMoment_Theta_CubicThetaLocalEnergyRellich`, `CubicMoment_Theta_CubicThetaLocalRellich`, `CubicMoment_Theta_CubicThetaLocalRellichValue`, `CubicMoment_Theta_CubicThetaMetricDerivative`, `CubicMoment_Theta_CubicThetaMetricScale`, `CubicMoment_Theta_CubicThetaMobiusGenerators`, `CubicMoment_Theta_CubicThetaPointMeasureLocallyFinite`, `CubicMoment_Theta_CubicThetaQuotientCharts`, `CubicMoment_Theta_CubicThetaSpatialDerivativeBound`, `CubicMoment_Theta_CubicThetaSupportedTangent`, `CubicMoment_Theta_CubicThetaTangentEnergy`, `CubicMoment_Theta_CubicThetaTangentIsometry`, `CubicMoment_Transform_MetaplecticAuxiliary`, `CubicMoment_Transform_MetaplecticHeight`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A000`, `OAIQ096A001` and `OAIQ096A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A007`, `OAIQ096A008`, `OAIQ096A009` and `OAIQ096A010`; the statements `OAI.CubicFirstMoment.SieveExponent.recurrence`, `OAI_CubicFirstMoment_UniformLogWeights_metaplectic_weighted_bilinear`, `OAI_CubicFirstMoment_angular_full_prime_product_height_bilinear`, `OAI_CubicFirstMoment_primeGroupTail_wide_bilinear_log_saving` and `OAI.CubicFirstMoment.sieveExponent_four_thirds`; the proof of `OAI_CubicFirstMoment_stopped_distinguished_full_saving`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A000
import Definitions.Def_OAIQ096A001
import Definitions.Def_OAIQ096A002

section
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
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
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2`

`L²` translation estimates for Euclidean `C¹_c` functions (and derived `H¹`) under invariant
measures.

This file lifts the pointwise fundamental-theorem-of-calculus bound from
`Euclidean.TranslationEstimate` to an `L²` bound using Tonelli and the measure-preserving property
of translations.

## Main results

- `enorm_translateL2_sub_toL2_le`: for `f ∈ C¹_c`, `‖τ_a f - f‖₂ ≤ ‖a‖ · ‖∇f‖₂` (as an `ℝ≥0∞`
  inequality on `L²` norms), under a right-invariant measure.
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

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2
variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceE_SobolevEuclideanTranslationEstimateL2
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddE_SobolevEuclideanTranslationEstimateL2
/-- `L²` translation estimate for `C¹_c` functions under a right-invariant measure. -/
lemma enorm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ₑ ≤
      ‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ := by
  classical
  -- Reduce to an `eLpNorm` inequality on representatives.
  have hL2 :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
          toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => (f.1 (x + a) - f.1 x)) (2 : ℝ≥0∞) μ := by
    -- Both terms agree a.e. with the underlying pointwise translation.
    have h₁ :
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) := by
      have hf :
          (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
        (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
      have hf' :
          (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
        exact
          (Measure.QuasiMeasurePreserving.ae_eq_comp
            (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
      exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
    have h₂ : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] fun x => f.1 x :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hsub :
        ((translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
              toL2 (μ := μ) (E := E) f : E →₂[μ] ℝ) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) - f.1 x := by
      filter_upwards [Lp.coeFn_sub
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f))
        (toL2 (μ := μ) (E := E) f), h₁, h₂] with x hxsub hx1 hx2
      simpa [hx1, hx2, Pi.sub_apply] using hxsub
    -- Convert the `Lp` norm to `eLpNorm` and rewrite using a.e. equality.
    let d : E →₂[μ] ℝ :=
      translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) - toL2 (μ := μ) (E := E) f
    have hd0 : (‖d‖ₑ : ℝ≥0∞) = MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have hd1 :
        MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) (by simpa [d] using hsub)
    simpa [d] using hd0.trans hd1
  have hGrad :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    have h₁ :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] fun x => grad (E := E) f.1 x :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have h0 :
        (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
          MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have h1 :
        MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) h₁
    exact h0.trans h1
  -- Prove the `eLpNorm` inequality by squaring, using Tonelli and measure-preserving translation.
  have hCore :
      MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ ≤
        ‖a‖ₑ * MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    -- Expand the definition of `eLpNorm` at exponent `2`.
    have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have h2_netop : (2 : ℝ≥0∞) ≠ ∞ := by simp
    simp_rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      h2_ne0 h2_netop, ENNReal.toReal_ofNat] at *
    -- It suffices to compare the squared integrals.
    have hsq :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
          ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
      -- Pointwise: Cauchy–Schwarz in `t`, then Tonelli in `(x,t)`.
      have hpt :
          ∀ x : E,
            ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
              ‖a‖ₑ ^ (2 : ℝ) *
                ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
        intro x
        have h0 := enorm_sub_le_enorm_mul_lintegral_grad (E := E) (x := x) (a := a) (f := f.1)
          (hf := f.2.1)
        -- Square both sides and apply Cauchy–Schwarz in `t`.
        have h1 :
            ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
              (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
          exact ENNReal.rpow_le_rpow h0 (by norm_num)
        have hcs :
            (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
          refine lintegral_rpow_two_le_lintegral_rpow_two (g := fun t : ℝ =>
            ‖grad (E := E) f.1 (x + t • a)‖ₑ) ?_
          -- measurability from continuity of `grad`.
          have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
          have hline : Continuous fun t : ℝ => x + t • a := by
            fun_prop
          exact (hgrad.comp hline).measurable.enorm.aemeasurable
        -- Combine and rewrite.
        calc
          ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ)
              ≤ (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := h1
          _ = ‖a‖ₑ ^ (2 : ℝ) *
              (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
              simpa using
                (ENNReal.mul_rpow_of_nonneg ‖a‖ₑ
                  (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                    ∂(μI : Measure ℝ))
                  (show (0 : ℝ) ≤ (2 : ℝ) by norm_num))
          _ ≤ ‖a‖ₑ ^ (2 : ℝ) *
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
                ∂(μI : Measure ℝ) := by
              gcongr
          _ = ‖a‖ₑ ^ (2 : ℝ) *
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
                ∂(μI : Measure ℝ) := rfl
      -- Integrate over `x` and apply Tonelli to swap integrals.
      let F : E × ℝ → ℝ≥0∞ :=
        fun z => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ ^ (2 : ℝ)
      have hmeas :
          AEMeasurable
            F (μ.prod (μI : Measure ℝ)) := by
        have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
        have hcont : Continuous fun z : E × ℝ => z.1 + z.2 • a := by
          fun_prop
        have hbase : Measurable fun z : E × ℝ => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ := by
          exact (hgrad.comp hcont).measurable.enorm
        have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
          (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
        exact (hpow.comp hbase).aemeasurable
      have hTonelli :
          (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) =
            ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
        -- Tonelli in both orders, via the product measure.
        have hprod :
            (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
              ∫⁻ x, ∫⁻ t, F (x, t) ∂(μI : Measure ℝ) ∂μ :=
          MeasureTheory.lintegral_prod (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
        have hprod_symm :
            (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
              ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) :=
          MeasureTheory.lintegral_prod_symm (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
        calc
          (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ)
              = ∫⁻ z, F z ∂μ.prod (μI : Measure ℝ) := by
                  simpa [F] using hprod.symm
          _ = ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) := hprod_symm
          _ = ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
                  simp [F]
      -- Now use measure-preserving translation in `x` and evaluate the `t`-integral.
      have hShift :
          (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) =
            ∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ) := by
        refine MeasureTheory.lintegral_congr fun t => ?_
        -- Change of variables `x ↦ x + t•a`.
        have hmeas' : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) := by
          have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
          have hbase : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ := hgrad.measurable.enorm
          have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
            (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
          exact hpow.comp hbase
        simpa [Function.comp, add_assoc] using
          (MeasureTheory.measurePreserving_add_right μ (t • a)).lintegral_comp (μ := μ) (ν := μ)
            (f := fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ)) hmeas'
      have hEval :
          (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) =
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
        -- `μI` has total mass `1`.
        simp [μI, Measure.restrict_apply, Real.volume_Icc]
      -- Put everything together.
      have hInt :
          (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
            ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
        calc
          (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ)
              ≤ ∫⁻ x, ‖a‖ₑ ^ (2 : ℝ) *
                    ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ := by
                refine MeasureTheory.lintegral_mono ?_
                intro x
                exact hpt x
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) := by
                -- Pull out the constant using `lintegral_const_mul''`.
                have hInner :
                    AEMeasurable
                      (fun x : E =>
                        ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) μ := by
                  -- Measurability of the inner integral follows
                  -- from `hmeas` via
                  -- `AEMeasurable.lintegral_prod_right'`.
                  simpa [F] using (hmeas.lintegral_prod_right' (μ := μ) (ν := (μI : Measure ℝ)))
                simpa [mul_assoc] using
                  (MeasureTheory.lintegral_const_mul'' (μ := μ) (r := ‖a‖ₑ ^ (2 : ℝ))
                    (f := fun x : E =>
                      ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) hInner)
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hTonelli
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hShift
          _ = ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hEval
      exact hInt
    -- Take the `1/2` power on both sides and simplify.
    have hsq' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ) * ∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      exact ENNReal.rpow_le_rpow hsq (by norm_num)
    -- Rewrite the RHS as `‖a‖ * (...)^(1/2)`.
    have hsq'' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      simpa [ENNReal.mul_rpow_of_nonneg, show (0 : ℝ) ≤ (1 / (2 : ℝ)) by nlinarith,
        mul_assoc, mul_left_comm, mul_comm] using hsq'
    have hroot : (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = ‖a‖ₑ := by
      -- `(x^2)^(1/2) = x` in `ℝ≥0∞`, accounting for simp-normalization of `2` and `1/2`.
      have hnat : (‖a‖ₑ ^ (2 : ℕ)) = ‖a‖ₑ ^ (2 : ℝ) := by
        simp
      calc
        (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = (‖a‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
          congrArg (fun r : ℝ≥0∞ => r ^ ((2 : ℝ)⁻¹)) hnat
        _ = ‖a‖ₑ := by
          have := (ENNReal.rpow_mul ‖a‖ₑ (2 : ℝ) ((2 : ℝ)⁻¹)).symm
          have hmul : (2 : ℝ) * ((2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
          simpa [hmul, ENNReal.rpow_one] using this
    simpa [hroot, mul_assoc, mul_left_comm, mul_comm] using hsq''
  -- Finish: translate back to the original `L²` norms.
  -- (The final `simp` is safe since we have explicit `eLpNorm` equalities above.)
  simpa [hL2, hGrad] using hCore

/-- Real-norm form of `enorm_translateL2_sub_toL2_le`. -/
lemma norm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ ≤
      ‖a‖ * ‖toL2Grad (μ := μ) (E := E) f‖ := by
  have h := enorm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hA_ne_top :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    simp [enorm]
  have hGrad_ne_top :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    simp [enorm]
  have hB_ne_top : (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    refine ENNReal.mul_ne_top ?_ hGrad_ne_top
    simp [enorm]
  have h' :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ).toReal ≤
        (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ).toReal := by
    exact (ENNReal.toReal_le_toReal hA_ne_top hB_ne_top).2 h
  simpa [ENNReal.toReal_mul, toReal_enorm'] using h'

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

section
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
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
-- module Solutions.OAIQ096_CM.Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
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
      exact ((dist_zero_right x).symm.le).trans hd
    have hTx' : ‖T x‖ ≤ C := by
      have hTx : ‖T x‖ ≤ C * ‖(x : H1vol)‖ := by
        have h :=
          (h1ToL2 (μ := (volume : Measure E)) (E := E)).le_opNorm (x : H1vol)
        exact h
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
      exact ((dist_zero_right x).symm.le).trans hd
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
-- module Solutions.OAIQ096_CM.CubicGram_EuclideanDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nearest-lattice division and the Eisenstein Euclidean domain. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

open UniqueFactorizationMonoid

lemma associated_normNat {x y : Eisenstein} (h : Associated x y) :
    normNat x = normNat y :=
  associated_iff_eq.mp (h.map normNatHom)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimeFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Squarefree factorization and exact prime detector products. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
def primeFactors (n : Eisenstein) : Finset Eisenstein := (normalizedFactors n).toFinset

lemma primeFactors_nodup {n : Eisenstein} (hn : Squarefree n) :
    (normalizedFactors n).Nodup :=
  (squarefree_iff_nodup_normalizedFactors hn.ne_zero).mp hn

def roughProduct (ψ : ℝ → ℝ) (y : ℝ) (n : Eisenstein) : ℝ :=
  ∏ p ∈ primeFactors n, (1 - ψ (norm p / y))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique primary associates and canonical prime factorization. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma primaryNormalize_injOn_primeFactors (n : Eisenstein) :
    Set.InjOn primaryNormalize (primeFactors n : Set Eisenstein) := by
  intro a ha b hb hab
  apply mem_normalizedFactors_eq_of_associated
    (Multiset.mem_toFinset.mp ha) (Multiset.mem_toFinset.mp hb)
  exact (primaryNormalize_associated a).trans (hab ▸ (primaryNormalize_associated b).symm)

def primaryPrimeFactors (n : Eisenstein) : Finset Eisenstein :=
  (primeFactors n).image primaryNormalize

lemma primaryPrimeFactor_spec {n p : Eisenstein} (hn : primary n)
    (hp : p ∈ primaryPrimeFactors n) : primaryPrime p ∧ p ∣ n := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hq' : q ∈ normalizedFactors n := Multiset.mem_toFinset.mp hq
  have hd : q ∣ n := dvd_of_mem_normalizedFactors hq'
  exact ⟨⟨primaryNormalize_primary (unit_residue_of_dvd_primary hn hd),
    prime_primaryNormalize (prime_of_normalized_factor q hq')⟩,
    (primaryNormalize_associated q).dvd_iff_dvd_left.mp hd⟩

lemma primary_finset_prod {ι : Type*} (s : Finset ι) (f : ι → Eisenstein)
    (hf : ∀ i ∈ s, primary (f i)) : primary (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primary]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact primary_mul (hf _ (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma primaryPrimeFactors_prod {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ∏ p ∈ primaryPrimeFactors n, p = n := by
  have heq : (∏ p ∈ primeFactors n, p) = (normalizedFactors n).prod := by
    rw [primeFactors, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr (primeFactors_nodup hs)]
    simp
  apply primary_associated_eq
    (primary_finset_prod _ _ (fun p hp => (primaryPrimeFactor_spec hn hp).1.1)) hn
  rw [primaryPrimeFactors, Finset.prod_image (primaryNormalize_injOn_primeFactors n)]
  exact ((Associated.prod _ _ _ (fun p _ => primaryNormalize_associated p)).symm).trans
    (heq ▸ prod_normalizedFactors hs.ne_zero)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_pos_of_ne_zero {a : Eisenstein} (ha : a ≠ 0) : 0 < norm a :=
  lt_of_le_of_ne (norm_nonneg a) (Ne.symm (norm_eq_zero_iff.not.mpr ha))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Conjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein conjugation, characters and Gauss-sum symmetry. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma additivePhase_neg {p : Eisenstein} (hp : p ≠ 0) (v : Eisenstein) :
    additivePhase p (-v) = star (additivePhase p v) := by
  let : Finite (Residues p) := finite_residues hp
  simpa only [← map_neg (Ideal.Quotient.mk (modulus p)), residueAddChar_mk, Complex.star_def] using
    (AddChar.map_neg_eq_conj (residueAddChar p hp) (Ideal.Quotient.mk (modulus p) v))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composite residue characters, Chinese remainders and squarefree Gauss norms. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

def gauss (b : Eisenstein) : ℂ :=
  (Real.sqrt (norm b) : ℂ)⁻¹ * ∑' v : Residues b,
    cubicSymbol b (residueRepresentative b v) * additivePhase b (residueRepresentative b v)

lemma gauss_prime {p : Eisenstein} (hp : primaryPrime p) : gauss p = gaussAtPrime p := by
  simp only [gauss, gaussAtPrime, cubicSymbol_prime hp]

lemma gauss_eq_finite_sum {b : Eisenstein} [Fintype (Residues b)] :
    gauss b = (Real.sqrt (norm b) : ℂ)⁻¹ * ∑ v : Residues b,
      cubicSymbol b (residueRepresentative b v) * additivePhase b (residueRepresentative b v) := by
  rw [gauss, tsum_fintype]

lemma cubicSymbol_add_last_lift {p d v w : Eisenstein} :
    cubicSymbol (p*p*d) (v+p*d*w) = cubicSymbol (p*p*d) v := by
  apply cubicSymbol_congr_prime_divisors
  intro q hq
  have hprime := prime_of_normalized_factor q hq
  have hd := dvd_of_mem_normalizedFactors hq
  have hqd : q ∣ p*d := by
    rcases hprime.dvd_or_dvd hd with hqq | hqd
    · rcases hprime.dvd_or_dvd hqq with hqp | hqp
      · exact dvd_mul_of_dvd_left hqp _
      · exact dvd_mul_of_dvd_left hqp _
    · exact dvd_mul_of_dvd_right hqd _
  simpa only [add_sub_cancel_left] using dvd_mul_of_dvd_left hqd w

lemma additivePhase_last_lift {p d : Eisenstein} (hp : p ≠ 0) (hd : d ≠ 0)
    (w : Eisenstein) : additivePhase (p*p*d) (p*d*w) = additivePhase p w := by
  have hp' : (p : ℂ) ≠ 0 := fun h => hp (Subtype.ext h)
  have hd' : (d : ℂ) ≠ 0 := fun h => hd (Subtype.ext h)
  have heq : ((p*d*w : Eisenstein) : ℂ) / ((p*p*d : Eisenstein) : ℂ) =
      (w : ℂ)/(p : ℂ) := by
    simp only [Subalgebra.coe_mul]
    field_simp
  simp only [additivePhase, heq]

def residueMix (a b : Eisenstein) (v : Residues a × Residues b) : Residues (a*b) :=
  Ideal.Quotient.mk (modulus (a*b))
    (b*residueRepresentative a v.1 + a*residueRepresentative b v.2)

lemma residueMix_injective {a b : Eisenstein} (hab : IsCoprime a b) :
    Function.Injective (residueMix a b) := by
  rintro ⟨x,y⟩ ⟨x',y'⟩ heq
  have hdiv : a*b ∣ (b*residueRepresentative a x+a*residueRepresentative b y)-
      (b*residueRepresentative a x'+a*residueRepresentative b y') :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp heq)
  apply Prod.ext
  · have hdiva := dvd_trans (dvd_mul_right a b) hdiv
    have hdivam : a ∣ a*(residueRepresentative b y-residueRepresentative b y') := dvd_mul_right _ _
    have hdivab : a ∣ b*(residueRepresentative a x-residueRepresentative a x') := by
      convert dvd_sub hdiva hdivam using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hx := residue_eq_of_dvd_sub (hab.dvd_of_dvd_mul_left hdivab)
    simpa only [residueRepresentative_spec] using hx
  · have hdivb := dvd_trans (dvd_mul_left b a) hdiv
    have hdivbm : b ∣ b*(residueRepresentative a x-residueRepresentative a x') := dvd_mul_right _ _
    have hdivba : b ∣ a*(residueRepresentative b y-residueRepresentative b y') := by
      convert dvd_sub hdivb hdivbm using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hy := residue_eq_of_dvd_sub (hab.symm.dvd_of_dvd_mul_left hdivba)
    simpa only [residueRepresentative_spec] using hy

lemma residueMix_bijective {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime a b) : Function.Bijective (residueMix a b) := by
  let : Finite (Residues a) := finite_residues ha
  let : Finite (Residues b) := finite_residues hb
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha hb)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨residueMix_injective hab, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_prod, residues_card ha, residues_card hb, residues_card (mul_ne_zero ha hb),
    normNat_mul]

lemma additivePhase_mix {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (v w : Eisenstein) :
    additivePhase (a*b) (b*v+a*w) = additivePhase a v * additivePhase b w := by
  have ha' : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  have hb' : (b : ℂ) ≠ 0 := fun h => hb (Subtype.ext h)
  rw [additivePhase_add]
  have hv : additivePhase (a*b) (b*v) = additivePhase a v := by
    have h : ((b*v : Eisenstein) : ℂ)/((a*b : Eisenstein) : ℂ) = (v : ℂ)/(a : ℂ) := by
      simp only [Subalgebra.coe_mul]
      field_simp
    simp only [additivePhase, h]
  have hw : additivePhase (a*b) (a*w) = additivePhase b w := by
    have h : ((a*w : Eisenstein) : ℂ)/((a*b : Eisenstein) : ℂ) = (w : ℂ)/(b : ℂ) := by
      simp only [Subalgebra.coe_mul]
      field_simp
    simp only [additivePhase, h]
  rw [hv,hw]

lemma cubicSymbol_mix {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (v w : Eisenstein) : cubicSymbol (a*b) (b*v+a*w) =
      cubicSymbol a b * cubicSymbol b a * (cubicSymbol a v * cubicSymbol b w) := by
  rw [cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero hb)]
  have hva : Ideal.Quotient.mk (modulus a) (b*v+a*w) = Ideal.Quotient.mk (modulus a) (b*v) := by
    apply residue_eq_of_dvd_sub
    simpa only [add_sub_cancel_left] using dvd_mul_right a w
  have hwb : Ideal.Quotient.mk (modulus b) (b*v+a*w) = Ideal.Quotient.mk (modulus b) (a*w) := by
    apply residue_eq_of_dvd_sub
    simpa only [add_sub_cancel_right] using dvd_mul_right b v
  rw [cubicSymbol_congr hva, cubicSymbol_congr hwb,
    cubicSymbol_mul_upper ha, cubicSymbol_mul_upper hb]
  ring

theorem gauss_mul_of_isCoprime {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) : gauss (a*b) =
      gauss a * gauss b * (cubicSymbol a b * cubicSymbol b a) := by
  have ha0 := primary_ne_zero ha
  have hb0 := primary_ne_zero hb
  let : Finite (Residues a) := finite_residues ha0
  let : Finite (Residues b) := finite_residues hb0
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha0 hb0)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b) (residueMix_bijective ha0 hb0 hab)
  let f (b : Eisenstein) (x : Residues b) : ℂ :=
    cubicSymbol b (residueRepresentative b x) * additivePhase b (residueRepresentative b x)
  have hmix (v : Residues a × Residues b) : f (a*b) (e v) =
      (cubicSymbol a b*cubicSymbol b a)*(f a v.1*f b v.2) := by
    have heq : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    dsimp only [f]
    rw [cubicSymbol_congr heq, additivePhase_congr (mul_ne_zero ha0 hb0) heq,
      cubicSymbol_mix ha hb, additivePhase_mix ha0 hb0]
    ring
  have hsum : (∑ x : Residues (a*b), f (a*b) x) =
      (cubicSymbol a b*cubicSymbol b a)*
      ((∑ x : Residues a, f a x)*(∑ y : Residues b, f b y)) := by
    rw [← Equiv.sum_comp e (f (a*b))]
    simp_rw [hmix]
    rw [← Finset.mul_sum, Fintype.sum_prod_type, ← Finset.sum_mul_sum]
  have hn : (Real.sqrt (norm (a*b)) : ℂ) =
      (Real.sqrt (norm a) : ℂ)*(Real.sqrt (norm b) : ℂ) := by
    have hn : norm (a*b) = norm a*norm b := by
      simp only [norm, Subalgebra.coe_mul, Complex.normSq_mul]
    rw [hn, Real.sqrt_mul (norm_nonneg a), Complex.ofReal_mul]
  simp only [gauss_eq_finite_sum]
  change (Real.sqrt (norm (a*b)) : ℂ)⁻¹*(∑ x, f (a*b) x) = _
  rw [hsum, hn, mul_inv_rev]
  change _ = ((Real.sqrt (norm a) : ℂ)⁻¹*(∑ x, f a x))*
    ((Real.sqrt (norm b) : ℂ)⁻¹*(∑ y, f b y))*(cubicSymbol a b*cubicSymbol b a)
  ring

lemma gauss_one : gauss 1 = 1 := by
  let : Finite (Residues (1 : Eisenstein)) := finite_residues one_ne_zero
  let : Fintype (Residues (1 : Eisenstein)) := Fintype.ofFinite _
  have hphase (v : Eisenstein) : additivePhase 1 v = 1 := by
    rw [additivePhase_congr one_ne_zero (residue_eq_of_dvd_sub (one_dvd (v-0))),
      additivePhase_zero]
  have hc : Fintype.card (Residues (1 : Eisenstein)) = 1 := by
    rw [← Nat.card_eq_fintype_card, residues_card one_ne_zero, normNat_one]
  simp [gauss_eq_finite_sum, cubicSymbol, normalizedFactors_one, hphase, hc, norm]

lemma primaryPrimes_isCoprime {p q : Eisenstein} (hp : primaryPrime p)
    (hq : primaryPrime q) (hne : p ≠ q) : IsCoprime p q := by
  apply isRelPrime_iff_isCoprime.mp
  apply hp.2.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hne (primary_associated_eq hp.1 hq.1 ((hp.2.dvd_prime_iff_associated hq.2).mp hd))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Reciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full cubic reciprocity and twisted multiplicativity of Gauss sums. -/

section

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicSymbolAtPrime_sq_eq_star {p : Eisenstein} (hp : primaryPrime p) (v : Eisenstein) :
    cubicSymbolAtPrime p v ^ 2 = star (cubicSymbolAtPrime p v) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  have hχ : cubicResidueChar p hp ^ 2 = (cubicResidueChar p hp)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, cubicResidueChar_cube hp]
  rw [← cubicResidueChar_mk p hp, ← MulChar.pow_apply' _ (by norm_num),
    hχ, MulChar.star_apply']

lemma cubicSymbol_sq_eq_star {b : Eisenstein} (hb : primary b) (v : Eisenstein) :
    cubicSymbol b v ^ 2 = star (cubicSymbol b v) := by
  revert v
  apply primary_induction (b := b) ?_ ?_ hb
  · intro v
    simp only [cubicSymbol_one_lower, one_pow, star_one]
  · intro p b hp hb ih v
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb), cubicSymbol_prime hp,
      mul_pow, cubicSymbolAtPrime_sq_eq_star hp, ih v, star_mul']

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FrequencyGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime, squarefree and mixed frequency Gauss evaluation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def frequencyGauss (b h : Eisenstein) : ℂ :=
  (Real.sqrt (norm b) : ℂ)⁻¹ * ∑' v : Residues b,
    cubicSymbol b (residueRepresentative b v) *
      additivePhase b (h * residueRepresentative b v)

lemma frequencyGauss_prime {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    frequencyGauss p h = star (cubicSymbol p h) * gauss p := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let χ := cubicResidueChar p hp
  let ψ := residueAddChar p hp.2.ne_zero
  let hbar := Ideal.Quotient.mk (modulus p) h
  have hsum : frequencyGauss p h = (Real.sqrt (norm p) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift hbar) := by
    unfold frequencyGauss gaussSum
    rw [tsum_fintype]
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [cubicSymbol_prime hp]
    change cubicSymbolAtPrime p (residueRepresentative p v) * _ =
      cubicSymbolAtPrime p (residueRepresentative p v) * _
    congr 1
    rw [AddChar.mulShift_apply]
    change additivePhase p (h * residueRepresentative p v) =
      residueAddChar p hp.2.ne_zero (hbar * v)
    have hvbar : hbar * v = Ideal.Quotient.mk (modulus p)
        (h * residueRepresentative p v) := by
      rw [map_mul, residueRepresentative_spec]
    rw [hvbar, residueAddChar_mk]
  have hc : χ hbar = cubicSymbol p h := by
    rw [cubicSymbol_prime hp]
    exact cubicResidueChar_mk p hp h
  have hgp : gauss p = (Real.sqrt (norm p) : ℂ)⁻¹ * gaussSum χ ψ := by
    rw [gauss_prime hp, gaussAtPrime_eq_gaussSum hp]
  rw [hsum, hgp, ← hc]
  by_cases hh : hbar = 0
  · have hzero : χ (0 : Residues p) = 0 := MulChar.map_zero χ
    rw [hh, AddChar.mulShift_zero,
      gaussSum_one_right (show χ ≠ 1 from cubicResidueChar_ne_one hp),
      hzero, star_zero, zero_mul, mul_zero]
  · let u : (Residues p)ˣ := Units.mk0 hbar hh
    change (Real.sqrt (norm p) : ℂ)⁻¹ * gaussSum χ (ψ.mulShift (u : Residues p)) = _
    rw [gaussSum_mulShift_eq]
    rw [← MulChar.star_apply']
    dsimp only [u, Units.val_mk0]
    ring

lemma frequencyGauss_mul_of_isCoprime {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hab : IsCoprime a b) (h : Eisenstein) :
    frequencyGauss (a*b) h = frequencyGauss a h * frequencyGauss b h *
      (cubicSymbol a b * cubicSymbol b a) := by
  have ha0 := primary_ne_zero ha
  have hb0 := primary_ne_zero hb
  let : Finite (Residues a) := finite_residues ha0
  let : Finite (Residues b) := finite_residues hb0
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha0 hb0)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b) (residueMix_bijective ha0 hb0 hab)
  let f (d : Eisenstein) (x : Residues d) : ℂ :=
    cubicSymbol d (residueRepresentative d x) *
      additivePhase d (h * residueRepresentative d x)
  have hmix (v : Residues a × Residues b) : f (a*b) (e v) =
      (cubicSymbol a b*cubicSymbol b a)*(f a v.1*f b v.2) := by
    have heq : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    have heqh : Ideal.Quotient.mk (modulus (a*b)) (h * residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (h * (b*residueRepresentative a v.1+a*residueRepresentative b v.2)) := by
      simp only [map_mul, heq]
    dsimp only [f]
    rw [cubicSymbol_congr heq, additivePhase_congr (mul_ne_zero ha0 hb0) heqh,
      cubicSymbol_mix ha hb]
    rw [show h * (b*residueRepresentative a v.1+a*residueRepresentative b v.2) =
      b*(h*residueRepresentative a v.1)+a*(h*residueRepresentative b v.2) by ring,
      additivePhase_mix ha0 hb0]
    ring
  have hsum : (∑ x : Residues (a*b), f (a*b) x) =
      (cubicSymbol a b*cubicSymbol b a)*
      ((∑ x : Residues a, f a x)*(∑ y : Residues b, f b y)) := by
    rw [← Equiv.sum_comp e (f (a*b))]
    simp_rw [hmix]
    rw [← Finset.mul_sum, Fintype.sum_prod_type, ← Finset.sum_mul_sum]
  have hn : (Real.sqrt (norm (a*b)) : ℂ) =
      (Real.sqrt (norm a) : ℂ)*(Real.sqrt (norm b) : ℂ) := by
    have hn : norm (a*b) = norm a*norm b := by
      simp only [norm, Subalgebra.coe_mul, Complex.normSq_mul]
    rw [hn, Real.sqrt_mul (norm_nonneg a), Complex.ofReal_mul]
  simp only [frequencyGauss, tsum_fintype]
  change (Real.sqrt (norm (a*b)) : ℂ)⁻¹*(∑ x, f (a*b) x) = _
  rw [hsum, hn, mul_inv_rev]
  change _ = ((Real.sqrt (norm a) : ℂ)⁻¹*(∑ x, f a x))*
    ((Real.sqrt (norm b) : ℂ)⁻¹*(∑ y, f b y))*(cubicSymbol a b*cubicSymbol b a)
  ring

lemma frequencyGauss_one (h : Eisenstein) : frequencyGauss 1 h = 1 := by
  let : Finite (Residues (1 : Eisenstein)) := finite_residues one_ne_zero
  let : Fintype (Residues (1 : Eisenstein)) := Fintype.ofFinite _
  have hphase (v : Eisenstein) : additivePhase 1 v = 1 := by
    rw [additivePhase_congr one_ne_zero (residue_eq_of_dvd_sub (one_dvd (v-0))),
      additivePhase_zero]
  have hc : Fintype.card (Residues (1 : Eisenstein)) = 1 := by
    rw [← Nat.card_eq_fintype_card, residues_card one_ne_zero, normNat_one]
  simp [frequencyGauss, tsum_fintype, cubicSymbol, normalizedFactors_one, hphase, hc, norm]

lemma frequencyGauss_prod_primaryPrimes (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) (h : Eisenstein) :
    frequencyGauss (∏ p ∈ s, p) h =
      star (cubicSymbol (∏ p ∈ s, p) h) * gauss (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frequencyGauss_one, gauss_one, cubicSymbol]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hprimary := primary_finset_prod s (fun q => q) (fun q hq => (hs q hq).1)
    have hc : IsCoprime p (∏ q ∈ s, q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun heq => hps (heq ▸ hq))
    rw [Finset.prod_insert hps,
      frequencyGauss_mul_of_isCoprime hp'.1 hprimary hc,
      frequencyGauss_prime hp', ih hs,
      cubicSymbol_mul_lower hp'.2.ne_zero (primary_ne_zero hprimary),
      gauss_mul_of_isCoprime hp'.1 hprimary hc, star_mul']
    ring

theorem frequencyGauss_squarefree {b : Eisenstein} (hb : primary b)
    (hs : Squarefree b) (h : Eisenstein) :
    frequencyGauss b h = star (cubicSymbol b h) * gauss b := by
  rw [← primaryPrimeFactors_prod hb hs]
  exact frequencyGauss_prod_primaryPrimes _
    (fun p hp => (primaryPrimeFactor_spec hb hp).1) h

def conjugateFrequencyGauss (b h : Eisenstein) : ℂ :=
  (Real.sqrt (norm b) : ℂ)⁻¹ * ∑' v : Residues b,
    star (cubicSymbol b (residueRepresentative b v)) *
      additivePhase b (h * residueRepresentative b v)

lemma conjugateFrequencyGauss_eq {b : Eisenstein} (hb : primary b)
    (h : Eisenstein) : conjugateFrequencyGauss b h = star (frequencyGauss b (-h)) := by
  let : Finite (Residues b) := finite_residues (primary_ne_zero hb)
  let : Fintype (Residues b) := Fintype.ofFinite _
  simp only [conjugateFrequencyGauss, frequencyGauss, tsum_fintype,
    star_mul', star_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro v hv
    rw [neg_mul, additivePhase_neg (primary_ne_zero hb), star_star]

lemma conjugateFrequencyGauss_squarefree {b : Eisenstein} (hb : primary b)
    (hs : Squarefree b) (h : Eisenstein) :
    conjugateFrequencyGauss b h = cubicSymbol b h * star (gauss b) := by
  rw [conjugateFrequencyGauss_eq hb, frequencyGauss_squarefree hb hs,
    cubicSymbol_neg hb, star_mul', star_star]

def mixedFrequencyGauss (a b h : Eisenstein) : ℂ :=
  (Real.sqrt (norm (a*b)) : ℂ)⁻¹ * ∑' v : Residues (a*b),
    (cubicSymbol a (residueRepresentative (a*b) v) *
       star (cubicSymbol b (residueRepresentative (a*b) v))) *
      additivePhase (a*b) (h * residueRepresentative (a*b) v)

lemma mixedFrequencyGauss_CRT {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hab : IsCoprime a b) (h : Eisenstein) :
    mixedFrequencyGauss a b h = frequencyGauss a h * conjugateFrequencyGauss b h *
      (cubicSymbol a b * star (cubicSymbol b a)) := by
  have ha0 := primary_ne_zero ha
  have hb0 := primary_ne_zero hb
  let : Finite (Residues a) := finite_residues ha0
  let : Finite (Residues b) := finite_residues hb0
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha0 hb0)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b) (residueMix_bijective ha0 hb0 hab)
  let f (x : Residues (a*b)) : ℂ :=
    (cubicSymbol a (residueRepresentative (a*b) x) *
      star (cubicSymbol b (residueRepresentative (a*b) x))) *
      additivePhase (a*b) (h * residueRepresentative (a*b) x)
  let fa (x : Residues a) : ℂ :=
    cubicSymbol a (residueRepresentative a x) * additivePhase a (h * residueRepresentative a x)
  let fb (x : Residues b) : ℂ :=
    star (cubicSymbol b (residueRepresentative b x)) * additivePhase b (h * residueRepresentative b x)
  have hmix (v : Residues a × Residues b) : f (e v) =
      (cubicSymbol a b * star (cubicSymbol b a)) * (fa v.1 * fb v.2) := by
    have heq : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    have hdiv : a*b ∣ residueRepresentative (a*b) (e v) -
        (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp heq)
    have heqa : Ideal.Quotient.mk (modulus a) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus a) (b*residueRepresentative a v.1) := by
      apply residue_eq_of_dvd_sub
      convert dvd_add (dvd_trans (dvd_mul_right a b) hdiv)
        (dvd_mul_right a (residueRepresentative b v.2)) using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have heqb : Ideal.Quotient.mk (modulus b) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus b) (a*residueRepresentative b v.2) := by
      apply residue_eq_of_dvd_sub
      convert dvd_add (dvd_trans (dvd_mul_left b a) hdiv)
        (dvd_mul_right b (residueRepresentative a v.1)) using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have heqh : Ideal.Quotient.mk (modulus (a*b)) (h * residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (h * (b*residueRepresentative a v.1+a*residueRepresentative b v.2)) := by
      simp only [map_mul, heq]
    dsimp only [f, fa, fb]
    rw [cubicSymbol_congr heqa, cubicSymbol_congr heqb,
      additivePhase_congr (mul_ne_zero ha0 hb0) heqh,
      cubicSymbol_mul_upper ha, cubicSymbol_mul_upper hb, star_mul']
    rw [show h * (b*residueRepresentative a v.1+a*residueRepresentative b v.2) =
      b*(h*residueRepresentative a v.1)+a*(h*residueRepresentative b v.2) by ring,
      additivePhase_mix ha0 hb0]
    ring
  have hsum : (∑ x : Residues (a*b), f x) =
      (cubicSymbol a b * star (cubicSymbol b a)) *
      ((∑ x : Residues a, fa x)*(∑ y : Residues b, fb y)) := by
    rw [← Equiv.sum_comp e f]
    simp_rw [hmix]
    rw [← Finset.mul_sum, Fintype.sum_prod_type, ← Finset.sum_mul_sum]
  have hn : (Real.sqrt (norm (a*b)) : ℂ) =
      (Real.sqrt (norm a) : ℂ)*(Real.sqrt (norm b) : ℂ) := by
    have hn : norm (a*b) = norm a*norm b := by
      simp only [norm, Subalgebra.coe_mul, Complex.normSq_mul]
    rw [hn, Real.sqrt_mul (norm_nonneg a), Complex.ofReal_mul]
  simp only [mixedFrequencyGauss, frequencyGauss, conjugateFrequencyGauss, tsum_fintype]
  change (Real.sqrt (norm (a*b)) : ℂ)⁻¹*(∑ x, f x) = _
  rw [hsum, hn, mul_inv_rev]
  change _ = ((Real.sqrt (norm a) : ℂ)⁻¹*(∑ x, fa x))*
    ((Real.sqrt (norm b) : ℂ)⁻¹*(∑ y, fb y))*(cubicSymbol a b*star (cubicSymbol b a))
  ring

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein real coordinates, measure factors and translated lattice Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

namespace CubicFirstMoment
open CubicPoisson

def traceFourier (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z : ℂ, (Real.fourierChar (-tracePair z w) : ℂ) * f z

lemma traceFourier_translation (f : ℂ → ℂ) (z w : ℂ) :
    traceFourier (fun x => f (z + x)) w =
      (Real.fourierChar (tracePair z w) : ℂ) * traceFourier f w := by
  have he (x : ℂ) : (Real.fourierChar (-tracePair x w) : ℂ) * f (z + x) =
      (Real.fourierChar (tracePair z w) : ℂ) *
        ((Real.fourierChar (-tracePair (z + x) w) : ℂ) * f (z + x)) := by
    rw [show -tracePair x w = tracePair z w + -tracePair (z + x) w by
      rw [tracePair_add_left]; ring, AddChar.map_add_eq_mul, Circle.coe_mul]
    rw [mul_assoc]
  simp only [traceFourier, he, integral_const_mul]
  rw [integral_add_left_eq_self (fun x : ℂ =>
    (Real.fourierChar (-tracePair x w) : ℂ) * f x) z]

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PeriodicPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic lattice Poisson summation and exact trace frequencies. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma additivePhase_fourierChar (p v : Eisenstein) :
    additivePhase p v = (Real.fourierChar (tracePair (v : ℂ) (1 / (p : ℂ))) : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold additivePhase tracePair
  dsimp only
  congr 1
  have hz : ∀ z : ℂ, z + star z = (2 * z.re : ℝ) := by
    intro z
    apply Complex.ext <;> simp
    ring
  rw [hz]
  push_cast
  rw [one_div, ← div_eq_mul_inv]
  ring

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MixedPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary mixed characters and squarefree coset Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mixedSymbol_mul {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (v w : Eisenstein) : mixedSymbol a b (v*w) = mixedSymbol a b v * mixedSymbol a b w := by
  simp only [mixedSymbol, cubicSymbol_mul_upper ha, cubicSymbol_mul_upper hb, star_mul']
  ring

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal character Gram kernel and normalized radial Poisson expansion. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

noncomputable section
open Filter
open scoped ContDiff

namespace CubicFirstMoment

def primaryCharacterGram (p p' : Eisenstein) (W : ℝ → ℂ) (Z : ℝ) : ℂ :=
  ∑' n : Eisenstein, if primary n then
    W (norm n / Z) * cubicSymbol p n * star (cubicSymbol p' n) else 0

def gramDyad (P : ℝ) (p : Eisenstein) : Prop :=
  primary p ∧ Squarefree p ∧ P ≤ norm p ∧ norm p < 2*P

def normProfileFourier (W : ℝ → ℂ) (y : ℂ) : ℂ :=
  (2 / Real.sqrt 3 : ℝ) • traceFourier (fun z => W (Complex.normSq z)) y

end CubicFirstMoment

namespace CubicFirstMoment

def radialDualProfile (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  normProfileFourier W (Real.sqrt t : ℂ)

end CubicFirstMoment
end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ideal Moebius weights and exact prime-factor subset identities. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
def idealMoebius (b : Eisenstein) : ℤ := UniqueFactorizationMonoid.moebius b

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic sieve operators, bilinear norms and coprime completion. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

open UniqueFactorizationMonoid

namespace CubicFirstMoment

def finiteCubicOperator (S H : Finset Eisenstein) :
    EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ H :=
  (Matrix.toEuclideanLin (fun (h : H) (a : S) => cubicSymbol a.val h.val)).toContinuousLinearMap

def finiteCubicBound (S H : Finset Eisenstein) : ℝ := ‖finiteCubicOperator S H‖^2

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated radial Mellin kernels with uniform rapid decay. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def gramLogKernel (W : ℝ → ℂ) (ρ u : ℝ) : ℂ :=
  gramLogBump u • normProfileFourier W ((Real.sqrt ρ * Real.exp (u/2) : ℝ) : ℂ)

lemma gramLogKernel_compact (W : ℝ → ℂ) (ρ : ℝ) :
    HasCompactSupport (gramLogKernel W ρ) :=
  gramLogBump.hasCompactSupport.smul_right

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin integral bounds for coprime radial forms. -/

section

noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimeRadialForm (S H : Finset Eisenstein) (v w phase : Eisenstein → ℂ)
    (x y : Eisenstein → ℝ) (W : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ∑ h ∈ H, phase h * ∑ a ∈ S, ∑ b ∈ S,
    if IsCoprime a b then
      (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) *
        radialDualProfile W (ρ*x h/(y a*y b)) else 0

def coprimeNormMajorant (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ) : ℝ :=
  ∑ s ∈ U.powerset,
    finiteCubicBound (S.filter (fun a => (∏ p ∈ s, p) ∣ a)) H *
      ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) +
       (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖^2)) / 2

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency dyads and summable base Gram recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def frequencyDyad (j : ℕ) : Finset Eisenstein :=
  (nonzeroNormBall ((2 : ℝ)^(j+1))).filter (fun h => Nat.log 2 (normNat h) = j)

end CubicFirstMoment

namespace CubicFirstMoment

def coprimeGramForm (S : Finset Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (Z : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    u a * star (u b) * primaryCharacterGram a b W Z else 0

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact common-factor row reindexing and matrix decomposition. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def residualRows (S : Finset Eisenstein) (k : Eisenstein) : Finset Eisenstein :=
  if hk : k ≠ 0 then S.preimage (k*·) (mul_right_injective₀ hk).injOn else ∅

def primaryCommonFactor (p q : Eisenstein) : Eisenstein :=
  ∏ r ∈ primaryPrimeFactors p ∩ primaryPrimeFactors q, r

def commonRowFactors (S : Finset Eisenstein) : Finset Eisenstein :=
  (S ×ˢ S).image (fun pq => primaryCommonFactor pq.1 pq.2)

def commonBlockCoefficient (u : Eisenstein → ℂ) (k m a : Eisenstein) : ℂ :=
  u (k*a) * cubicSymbol a m

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary cube decomposition and finite operator block bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_of_primary_mul_left {a b : Eisenstein} (ha : primary a)
    (hab : primary (a*b)) : primary b := by
  rw [primary_iff_residue_one] at ha hab ⊢
  simpa only [map_mul, ha, one_mul] using hab

theorem primary_cube_decomposition {n : Eisenstein} (hn : primary n) :
    ∃ s t c : Eisenstein, primary s ∧ primary t ∧ primary c ∧
      Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧ n = s*t^2*c^3 := by
  apply primary_induction (b := n) ?_ ?_ hn
  · refine ⟨1,1,1,?_,?_,?_,squarefree_one,squarefree_one,isCoprime_one_left,?_⟩ <;>
      simp [primary]
  · intro p b hp hb ih
    obtain ⟨s,t,c,hs,ht,hc,hss,hst,hcop,rfl⟩ := ih
    by_cases hps : p ∣ s
    · obtain ⟨s',rfl⟩ := hps
      have hs' := primary_of_primary_mul_left hp.1 hs
      have hps' : IsCoprime p s' :=
        isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hss).1
      have hpt : IsCoprime p t := hcop.of_mul_left_left
      refine ⟨s',p*t,c,hs',primary_mul hp.1 ht,hc,hss.of_mul_right,
        squarefree_mul_iff.mpr ⟨hpt.isRelPrime,hp.2.squarefree,hst⟩,
        hps'.symm.mul_right hcop.of_mul_left_right,?_⟩
      ring
    · by_cases hpt : p ∣ t
      · obtain ⟨t',rfl⟩ := hpt
        refine ⟨s,t',p*c,hs,primary_of_primary_mul_left hp.1 ht,primary_mul hp.1 hc,
          hss,hst.of_mul_right,hcop.of_mul_right_right,?_⟩
        ring
      · have hps' := hp.2.coprime_iff_not_dvd.mpr hps
        have hpt' := hp.2.coprime_iff_not_dvd.mpr hpt
        refine ⟨p*s,t,c,primary_mul hp.1 hs,ht,hc,
          squarefree_mul_iff.mpr ⟨hps'.isRelPrime,hp.2.squarefree,hss⟩,
          hst,hpt'.mul_left hcop,?_⟩
        ring

end CubicFirstMoment

namespace CubicFirstMoment

def cubeBlockMass (P S T C : Finset Eisenstein) (u : Eisenstein → ℂ) : ℝ :=
  ∑ s ∈ S, ∑ t ∈ T, ∑ c ∈ C,
    ‖∑ b ∈ P, u b * cubicSymbol b (s*t^2*c^3)‖^2

end CubicFirstMoment

namespace CubicFirstMoment

def cubeBlockSupport (S T C : Finset Eisenstein) : Finset Eisenstein :=
  (S.product (T.product C)).image (fun z => z.1*z.2.1^2*z.2.2^3)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramified residual factors and full cube decomposition. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def residualCubeSupport (R S T C : Finset Eisenstein) : Finset Eisenstein :=
  R.biUnion fun r => (cubeBlockSupport S T C).image (r * ·)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric decay, cube frequency dyads and numerical block inequalities. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreePrimaryDyad (j : ℕ) : Finset Eisenstein :=
  (frequencyDyad j).filter (fun n => primary n ∧ Squarefree n)

def cubeFrequencyCover (j : ℕ) : Finset Eisenstein :=
  (cubeDyadTriples j).biUnion (fun z => residualCubeSupport (nonzeroNormBall 729)
    (squarefreePrimaryDyad z.1) (squarefreePrimaryDyad z.2.1) (frequencyDyad z.2.2))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GlobalRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summed dual norms and full smoothed sieve recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def dualDyadicNorm (S : Finset Eisenstein) (c : ℝ) (A : ℕ) : ℝ :=
  ∑' j : ℕ, finiteCubicBound S (frequencyDyad j) / (1+c*2^j)^A

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def commonBlockEnergy (S : Finset Eisenstein) (u : Eisenstein → ℂ) (k : Eisenstein) : ℝ :=
  ∑ a ∈ residualRows S k, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u (k*a)‖^2

def commonBlockCost (S : Finset Eisenstein) (W : ℝ → ℂ) (Z N : ℝ) (A : ℕ)
    (k m : Eisenstein) : ℝ :=
  if norm k < N then
    ((Z/norm m)/(N/norm k)) *
      dualDyadicNorm (residualRows S k) ((Z/norm m)/(27*(N/norm k)^2)) A
  else ‖primaryCharacterGram 1 1 W (Z/norm m)‖

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative cube and dual bounds under a sieve exponent. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def SieveExponent (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ b ∈ H, primary b ∧ Squarefree b ∧ norm b ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^ε*(M+(M*N)^(2/3 : ℝ)+N^ξ)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_InnerExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full inner cube covers and sharp coefficient extension bounds. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev InnerCubeIndex := (_index : ℕ×ℕ×ℕ) × (Eisenstein×Eisenstein×Eisenstein×Eisenstein)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedHecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-order Hecke prime input

The finite-order Hecke prime-sum input specializes to independent prime
factors using the elementary character laws.

The input is the cubic-character consequence of Thorner--Zaman,
*A unified and improved Chebotarev density theorem*, Algebra & Number
Theory 13 (2019), Theorem 1.4, in the Siegel–Walfisz form for cubic Hecke characters.  Only finite-order characters occur in this input;
smooth weights and norm twists follow by partial summation.
-/

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CubicFirstMoment

/-- Excludes the principal character on ideals prime to the conductor. -/
def MixedCubicNonprincipal (q₁ q₂ : Eisenstein) : Prop :=
  ∃ a : Eisenstein, primary a ∧ IsCoprime (q₁ * q₂) a ∧ mixedCubic q₁ q₂ a ≠ 1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact corrected-dispersion identities

The polynomials below are those in `eq:dispersion-polynomials` of the
manuscript. The factorization is valid even with a common prime factor:
the already proved Gauss-sum multiplication law then makes the summand zero.
The norm estimates here do not assume the new dispersion bounds.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

/-- The polynomial `F_u(a)` in the corrected-dispersion argument. -/
def dispersionPolynomial (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (a : Eisenstein) : ℂ :=
  ∑ b ∈ B, β b * normTwist u b * gauss b * star (cubicSymbol b a)

/-- The model polynomial `S(u)`. -/
def dispersionModel (B : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  ∑ b ∈ B, β b * normTwist u b * ((norm b ^ (-1 / 6 : ℝ) : ℝ) : ℂ)

/-- The corrected row polynomial. -/
def correctedDispersionPolynomial (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (a : Eisenstein) : ℂ :=
  dispersionPolynomial B β u a -
    (cStar : ℂ) * star (gauss a) * ((norm a ^ (-1 / 6 : ℝ) : ℝ) : ℂ) *
      dispersionModel B β u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeFunctionalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebra of the published primitive Hecke functional equation.
The completion uses A = sqrt(3 D)/(2 pi), where D is the ideal conductor
norm. See Watkins (2011), Section 3.6, and Rajan (1998), Section 1,
pp. 281--283 for the fixed infinity-type completion. The uncompleted and symmetry-line identities follow from that exact equation. -/

noncomputable section
namespace CubicFirstMoment

/-- The precisely normalized functional-equation input, supplied for an
actual primitive character and its contragredient, away from the gamma
poles. The regular-point restriction is necessary because mathlib
totalizes Gamma at its poles; the analytic completion has removable
singularities there, whereas the pointwise product need not agree. -/
def HeckeFunctionalEquation (A k : ℝ) (ε : ℂ) (L Ldual : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, Complex.Gamma (s+(k:ℂ)) ≠ 0 →
    Complex.Gamma (1-s+(k:ℂ)) ≠ 0 →
    heckeCompleted A k L s = ε*heckeCompleted A k Ldual (1-s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergent norm series on the Eisenstein lattice

These elementary lattice bounds provide a quantitative tail for the
Möbius residue sum after square-divisor truncation.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment

lemma eisenstein_norm_eq_sq (a : Eisenstein) : norm a = ‖a‖^2 :=
  (Complex.sq_norm (a : ℂ)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDualContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained finite dual polynomials for fixed infinity type. The sole
Gamma strip input is the bounded-strip consequence of NIST DLMF 5.11.9;
there is no arithmetic moment or smooth-duality conclusion in that input. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def angularFiniteHeckeDual {ι : Type*} (S : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (ε : ℂ) (A k : ℝ) (s : ℂ) : ℂ :=
  ε*(A:ℂ)^(1-2*s)*angularGammaFEQuotient k s*finiteNormDirichlet S a N (1-s)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler products identify and bound the arithmetic Möbius coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def finiteIdealMoebius (S : Finset EisensteinIdealPrime) : EisensteinArithmeticFunction :=
  ∏ p ∈ S, (1 - MvPowerSeries.X p)

lemma coeff_mul_one_sub_X (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν (A * (1 - MvPowerSeries.X p)) =
      MvPowerSeries.coeff ν A -
        if 1 ≤ ν p then MvPowerSeries.coeff (ν - Finsupp.single p 1) A else 0 := by
  rw [mul_sub, mul_one, map_sub, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial]
  simp only [Finsupp.single_le_iff, mul_one]

lemma tsub_single_away (S : Finset EisensteinIdealPrime)
    {p : EisensteinIdealPrime} (hp : p ∉ S) (ν : EisensteinIdealExponent) :
    (∀ q ∈ S, (ν - Finsupp.single p 1 : EisensteinIdealExponent) q = 0) ↔ ∀ q ∈ S, ν q = 0 := by
  apply forall₂_congr
  intro q hq
  simp [Finsupp.tsub_apply, ne_of_mem_of_not_mem hq hp]

/-- Normalized prime representatives identify the exponent multiset
with the existing normalized factorization of an Eisenstein element. -/
lemma idealPrimeFactors_normalized (a : Eisenstein) :
    (Associates.factors' a).map (fun p => p.val.out) =
      UniqueFactorizationMonoid.normalizedFactors a := by
  calc
    _ = ((Associates.factors' a).map Subtype.val).map
        (Associates.out : Associates Eisenstein → Eisenstein) :=
      (Multiset.map_map _ _ _).symm
    _ = _ := by
      rw [Associates.map_subtype_coe_factors', Multiset.map_map]
      rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite ordered prime convolutions used in the exceptional moments.
The weights are independent on the prime factors; the squarefree cutoff
is exposed exactly as the repeated-prime discrepancy. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def orderedConvolutionSupport (S : ι → Finset Eisenstein) : Finset Eisenstein :=
  (Fintype.piFinset S).image (fun f => ∏ i, f i)

def orderedConvolution (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    (b : Eisenstein) : ℂ :=
  ∑ f ∈ Fintype.piFinset S with (∏ i, f i) = b, ∏ i, w i (f i)

def squarefreeConvolution (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    (b : Eisenstein) : ℂ :=
  if Squarefree b then orderedConvolution S w b else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial strip growth for the shifted completion Gamma(s+k).
The input is the ordinary entire order-one completion, expressed by a
coarse quadratic exponential bound. All strip bounds are derived. -/
noncomputable section
open Set
namespace CubicFirstMoment

def ShiftedCompletedHeckeFiniteOrder (A k : ℝ) (L : ℂ → ℂ) : Prop :=
  ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
    (∀ s : ℂ, Complex.Gamma (s+(k:ℂ)) ≠ 0 → Λ s = heckeCompleted A k L s) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖Λ s‖ ≤ Real.exp (C*(1+‖s‖)^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-angular metaplectic inputs, stated for the literal Gauss series.

Sources: Heath-Brown, *Kummer's conjecture for cubic Gauss sums* (2000),
§3 Lemma 3 (author manuscript p.9), with angular index zero; Dunn–Radziwiłł,
*Bias in cubic Gauss sums* (2024), arXiv:2109.07463v3, Proposition 5.2,
pp.29–30. No Type-I estimate or Mellin contour identity is an input here. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev PrimaryArgument := {u : Eisenstein // primary u}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact expansion of the dispersion variance

The two independent coefficient variables produce the mixed cubic character
in the lattice variable. This is the algebraic starting point for applying
Poisson summation, before separating cube and noncube frequencies.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

def dispersionAmplitude (β : Eisenstein → ℂ) (u : ℝ) (b : Eisenstein) : ℂ :=
  β b * normTwist u b * gauss b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collecting the squarefree majorant by least common multiples

The join is the product of the union of the primary prime factors. Its
square divides an element exactly when both input squares divide it.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primarySquarefreeJoin (a b : Eisenstein) : Eisenstein :=
  ∏ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, p

def collectedSquarefreeSieveCoefficient (C : Finset Eisenstein) (e : Eisenstein) : ℝ :=
  ∑ t ∈ (C.product C).filter (fun t => primarySquarefreeJoin t.1 t.2 = e),
    (idealMoebius t.1 : ℝ)*(idealMoebius t.2 : ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeightFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Mellin estimates for the smooth weight families occurring in
Type I. The hypotheses state common support and derivative bounds in
logarithmic coordinates. No transform or moment estimate is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform BigOperators
namespace CubicFirstMoment

/-- A fixed test function, with any index set, has the required uniform
support and derivative bounds. -/
def uniformLogWeights_constant {ι : Type*} (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) : UniformLogWeights (fun _ : ι => W) := by
  let hex := (logPullback_compact W hW hpos).isCompact.isBounded.exists_norm_le
  let R := Classical.choose hex
  have hR := Classical.choose_spec hex
  let G := mellinLogSchwartz W hW hpos hsm 0
  refine ⟨fun _ => hW,fun _ => hpos,fun _ => hsm,max R 0,le_max_right _ _,?_,?_⟩
  · intro i u hu
    have huR : |u| ≤ R := by simpa only [Real.norm_eq_abs] using hR u hu
    exact huR.trans (le_max_left _ _)
  · intro n
    refine ⟨SchwartzMap.seminorm ℝ 0 n G,by positivity,?_⟩
    intro i u
    have he : (G : ℝ → ℂ) = fun v : ℝ => W (Real.exp (-v)) := by
      ext v
      simp [G,mellinLogSchwartz_apply]
    rw [← he]
    simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm ℝ 0 n G u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularWeightOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed continuous operator from logarithmic test functions to plane
annuli. It makes the angular lattice bounds uniform over the given weights. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology SchwartzMap
namespace CubicFirstMoment

lemma UniformLogWeights.annular_support {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (i : ι) :
    tsupport (W i) ⊆ Icc (Real.exp (-h.radius)) (Real.exp h.radius) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hp : 0 < x := h.positive i (subset_tsupport _ hx)
  have hu : -Real.log x ∈ tsupport (fun v => W i (Real.exp (-v))) := by
    apply subset_tsupport
    simpa only [Function.mem_support,neg_neg,Real.exp_log hp] using hx
  have he := abs_le.mp (h.support_bound i (-Real.log x) hu)
  constructor
  · have ht := Real.exp_le_exp.mpr (show -h.radius ≤ Real.log x by linarith)
    simpa only [Real.exp_log hp] using ht
  · have ht := Real.exp_le_exp.mpr (show Real.log x ≤ h.radius by linarith)
    simpa only [Real.exp_log hp] using ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CompactParameterWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact smooth parameter family inherits uniform logarithmic
weight estimates from its joint derivatives. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CubicFirstMoment

/-- Only compactness of the parameter range, joint smoothness and common
support are needed; no Mellin estimate is assumed. -/
def uniformLogWeights_compactParameter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : Set E) (hK : IsCompact K)
    (W : E → ℝ → ℂ) (w : ℝ → ℂ)
    (hw : HasCompactSupport w) (hpos : tsupport w ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ w)
    (hW : ContDiff ℝ ∞ (Function.uncurry W))
    (hsupp : ∀ p ∈ K, Function.support (W p) ⊆ Function.support w) :
    UniformLogWeights (fun p : K => W p) := by
  let hconst := uniformLogWeights_constant (ι := Unit) w hw hpos hsm
  let F : E × ℝ → ℂ := fun z => W z.1 (Real.exp (-z.2))
  have he : ContDiff ℝ ∞ (fun z : E × ℝ => (z.1,Real.exp (-z.2))) := by fun_prop
  have hF : ContDiff ℝ ∞ F := hW.comp he
  have hlog (p : K) : tsupport (fun v => W p (Real.exp (-v))) ⊆
      tsupport (fun v => w (Real.exp (-v))) := by
    exact closure_mono (fun v hv => hsupp p p.property hv)
  refine ⟨fun p => hw.mono (hsupp p p.property),
    fun p => (closure_mono (hsupp p p.property)).trans hpos,
    fun p => hW.comp (contDiff_const.prodMk contDiff_id),
    hconst.radius,hconst.radius_nonneg,?_,?_⟩
  · intro p u hu
    exact hconst.support_bound () u (hlog p hu)
  · intro n
    let T := K ×ˢ Icc (-hconst.radius) hconst.radius
    have hT : IsCompact T := hK.prod isCompact_Icc
    obtain ⟨C,hC⟩ := hT.exists_bound_of_continuousOn
      ((hF.continuous_iteratedFDeriv (show (n:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).continuousOn)
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro p u
    by_cases hu : |u| ≤ hconst.radius
    · exact (norm_iteratedFDeriv_slice_le F hF p u n).trans
        ((hC (p,u) ⟨p.property,abs_le.mp hu⟩).trans (le_max_left _ _))
    · have hz : iteratedFDeriv ℝ n (fun v => W p (Real.exp (-v))) u = 0 := by
        by_contra hn
        have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
          (f := fun v => W p (Real.exp (-v))) n hn
        exact hu (hconst.support_bound () u (hlog p hs))
      rw [hz,norm_zero]
      exact le_max_right _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformWeightCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and finite-coordinate assembly for uniform smooth weights. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

 def UniformLogWeights.reindex {α β : Type*} {W : α → ℝ → ℂ}
    (h : UniformLogWeights W) (f : β → α) : UniformLogWeights (fun b => W (f b)) where
  compact b := h.compact (f b)
  positive b := h.positive (f b)
  smooth b := h.smooth (f b)
  radius := h.radius
  radius_nonneg := h.radius_nonneg
  support_bound b u hu := h.support_bound (f b) u hu
  derivative_bound n := by
    obtain ⟨B,hB,hbound⟩ := h.derivative_bound n
    exact ⟨B,hB,fun b u => hbound (f b) u⟩

 def UniformLogWeights.finiteCoordinates {γ ι : Type*} [Fintype ι]
    (W : γ → ι → ℝ → ℂ) (h : ∀ i, UniformLogWeights (fun u => W u i)) :
    UniformLogWeights (fun z : γ × ι => W z.1 z.2) where
  compact z := (h z.2).compact z.1
  positive z := (h z.2).positive z.1
  smooth z := (h z.2).smooth z.1
  radius := ∑ i, (h i).radius
  radius_nonneg := Finset.sum_nonneg (fun i _ => (h i).radius_nonneg)
  support_bound z u hu := ((h z.2).support_bound z.1 u hu).trans
    (Finset.single_le_sum (fun i _ => (h i).radius_nonneg) (Finset.mem_univ z.2))
  derivative_bound n := by
    choose B hB hbound using fun i => (h i).derivative_bound n
    refine ⟨∑ i, B i,Finset.sum_nonneg (fun i _ => hB i),?_⟩
    intro z u
    exact (hbound z.2 z.1 u).trans
      (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ z.2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformWeightMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform support and derivative bounds survive the compact family
of logarithmic-denominator multipliers used in the original coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

 def UniformLogWeights.compactMultiplier {γ E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W : γ → ℝ → ℂ} (h : UniformLogWeights W)
    (K : Set E) (hK : IsCompact K) (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    UniformLogWeights (fun z : γ × K => fun x => F z.2 x*W z.1 x) := by
  let G : E × ℝ → ℂ := fun z => F z.1 (Real.exp (-z.2))
  have hmap : ContDiff ℝ ∞ (fun z : E × ℝ => (z.1,Real.exp (-z.2))) := by fun_prop
  have hG : ContDiff ℝ ∞ G := hF.comp hmap
  have hbound (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : K, ∀ u : ℝ, |u| ≤ h.radius →
      ‖iteratedFDeriv ℝ n (fun v => F p (Real.exp (-v))) u‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hK.prod (isCompact_Icc (a := -h.radius) (b := h.radius))).exists_bound_of_continuousOn
      ((hG.continuous_iteratedFDeriv (show (n:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).continuousOn)
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro p u hu
    exact (norm_iteratedFDeriv_slice_le G hG p u n).trans
      ((hC (p,u) ⟨p.property,abs_le.mp hu⟩).trans (le_max_left _ _))
  choose C hC hCb using hbound
  choose B hB hBb using h.derivative_bound
  refine ⟨fun z => (h.compact z.1).mono (Function.support_mul_subset_right _ _),
    fun z => tsupport_mul_subset_right.trans (h.positive z.1),
    fun z => (hF.comp (contDiff_const.prodMk contDiff_id)).mul (h.smooth z.1),
    h.radius,h.radius_nonneg,?_,?_⟩
  · intro z u hu
    exact h.support_bound z.1 u (tsupport_mul_subset_right hu)
  · intro n
    let A := ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*C j*B (n-j)
    have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j)) (hB (n-j)))
    refine ⟨A,hA,?_⟩
    intro z u
    by_cases hu : |u| ≤ h.radius
    · have hf : ContDiff ℝ ∞ (fun v => F z.2 (Real.exp (-v))) :=
        hG.comp (contDiff_const.prodMk contDiff_id)
      have hw : ContDiff ℝ ∞ (fun v => W z.1 (Real.exp (-v))) :=
        (h.smooth z.1).comp (by fun_prop)
      apply (norm_iteratedFDeriv_mul_le hf hw u (by exact_mod_cast le_top : (n:ℕ∞ω) ≤ ∞)).trans
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hCb j z.2 u hu) (Nat.cast_nonneg _))
        (hBb (n-j) z.1 u) (_root_.norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC j))
    · have hz : iteratedFDeriv ℝ n (fun v => F z.2 (Real.exp (-v))*W z.1 (Real.exp (-v))) u = 0 := by
        by_contra hn
        have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
          (f := fun v => F z.2 (Real.exp (-v))*W z.1 (Real.exp (-v))) n hn
        exact hu (h.support_bound z.1 u (tsupport_mul_subset_right hs))
      rw [hz,norm_zero]
      exact hA

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicWeightFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial logarithmic derivative cost can be normalized by any
fixed positive power of the outer length. This gives a uniform smooth
family without discarding the original, varying test functions. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

 def LogarithmicWeightFamily.normalize {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (h : LogarithmicWeightFamily Y W) {s : ℝ} (hs : 0 < s) :
    UniformLogWeights (normalizedLogWeight Y W s) := by
  have hsupp (i : γ) : Function.support (normalizedLogWeight Y W s i) ⊆ Function.support (W i) := by
    intro x hx
    by_contra hz
    have he : W i x = 0 := by simpa only [Function.mem_support,not_not] using hz
    exact hx (by simp [normalizedLogWeight,he])
  refine ⟨fun i => (h.compact i).mono (hsupp i),
    fun i => (closure_mono (hsupp i)).trans (h.positive i),
    fun i => (h.smooth i).const_smul _,h.radius,h.radius_nonneg,?_,?_⟩
  · intro i u hu
    apply h.support_bound i u
    exact closure_mono (fun x hx => by
      intro hz
      exact hx (by simp [normalizedLogWeight,hz])) hu
  · intro n
    obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound n
    obtain ⟨K,hK,hKbound⟩ := log_power_normalization_bound A hs
    refine ⟨C*K,mul_nonneg hC hK,?_⟩
    intro i u
    have hw : ContDiff ℝ ∞ (fun v => W i (Real.exp (-v))) :=
      (h.smooth i).comp (by fun_prop)
    have hYp : 0 < Y i := zero_lt_one.trans_le (h.length_one i)
    change ‖iteratedFDeriv ℝ n (fun v => (Y i^(-s):ℝ) • W i (Real.exp (-v))) u‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hw.of_le (by exact_mod_cast le_top)).contDiffAt),
      norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hYp.le _)]
    calc
      _ ≤ Y i^(-s)*(C*(1+Real.log (Y i))^A) :=
        mul_le_mul_of_nonneg_left (hbound i u) (Real.rpow_nonneg hYp.le _)
      _ = C*(Y i^(-s)*(1+Real.log (Y i))^A) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hKbound (Y i) (h.length_one i)) hC

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPowerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed real powers preserve the actual positive annular weight family.
The smooth extension used in the proof agrees with the power wherever
the original weight is nonzero. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def UniformLogWeights.realPower {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (q : ℝ) :
    UniformLogWeights (fun i x => ((x^q:ℝ):ℂ)*W i x) := by
  let a := Real.exp (-h.radius)
  let b := Real.exp h.radius
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  let g := angularLogExtension a b
  have hg : ContDiff ℝ ∞ g := contDiff_id.add (angularLogPerturbation_smooth ha hb)
  let F : ℝ → ℝ → ℂ := fun _ x => (Real.exp (-q*g x):ℂ)
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    change ContDiff ℝ ∞ (fun p : ℝ × ℝ => (Real.exp (-q*g p.2):ℂ))
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_const.mul (hg.comp contDiff_snd)))
  let hh := h.compactMultiplier ({0}:Set ℝ) isCompact_singleton F hF
  have hi := hh.reindex (fun i => (i,⟨0,by simp⟩))
  have he : (fun i (x : ℝ) => ((x^q:ℝ):ℂ)*W i x) =
      (fun i x => F 0 x*W i x) := by
    funext i x
    by_cases hw : W i x = 0
    · simp only [hw,mul_zero]
    · have hx := h.annular_support i (subset_tsupport (W i) hw)
      have hxp : 0 < x := lt_of_lt_of_le ha hx.1
      have hlog : g x = -Real.log x := angularLogExtension_eq_log ha hb hx
      dsimp only [F]
      rw [hlog,Real.rpow_def_of_pos hxp]
      rw [show Real.log x*q = -q*(-Real.log x) by ring]
  rw [he]
  exact hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RepeatedPrimeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree prime-convolution discrepancy has sparse support.
This supplies the support saving before the character-moment estimates. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squarefreeConvolutionError (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) : ℂ :=
  orderedConvolution S w b-squarefreeConvolution S w b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeAsymptotic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral main term of the principal cube lattice. -/

noncomputable section
open scoped BigOperators SchwartzMap ContDiff
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The normalized planar integral; the measure of an Eisenstein
fundamental parallelogram is one. -/
def cubeProfileIntegral (W : ℝ → ℂ) : ℂ :=
  (2/Real.sqrt 3:ℝ) • ∫ z : ℂ, normProfileFourier W (z^3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GaussianTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Fourier kernels with the Eisenstein trace normalization. -/

noncomputable section
open scoped FourierTransform
open MeasureTheory
namespace CubicFirstMoment

lemma traceFourier_eq_fourier (f : ℂ → ℂ) (w : ℂ) :
    traceFourier f w = 𝓕 f (2*star w) := by
  rw [Real.fourier_eq,traceFourier]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Circle.smul_def,smul_eq_mul]
  congr 2
  simp only [real_inner_eq_re_inner ℂ,RCLike.inner_apply,tracePair,
    Complex.star_def,RCLike.re_to_complex,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.re_ofNat,Complex.im_ofNat]
  congr 1
  ring

/-- The trace pairing doubles the usual Fourier frequency. -/
theorem traceFourier_gaussian {t : ℝ} (ht : 0 < t) (w : ℂ) :
    traceFourier (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) w =
      (Real.pi/t:ℝ) * Complex.exp ((-4*Real.pi^2/t*Complex.normSq w:ℝ):ℂ) := by
  rw [traceFourier_eq_fourier]
  have h := fourier_gaussian_innerProductSpace (b := (t:ℂ))
    (by simpa using ht) (2*star w)
  rw [h]
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℂ) ≠ 0),
    Complex.cpow_one]
  rw [Complex.ofReal_div]
  congr 2
  simp only [norm_mul,norm_star,Complex.normSq_eq_norm_sq]
  norm_num
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation on the entire fixed norm range of a prime
convolution. The cutoff belongs to the transform, so no cutoff is inserted
into the arithmetic coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def wideGramLogKernel (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (ρ u : ℝ) : ℂ :=
  wideGramLogBump M hM u • normProfileFourier W ((Real.sqrt ρ*Real.exp (u/2):ℝ):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticAuxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The auxiliary functions in Heath-Brown (2000), §3, equations (14)
and (19), and the finite-divisor estimate on author-manuscript p.14.
Only fixed-level strip growth is needed here, so the finite-divisor
estimate drops its factors at most one. All polynomial estimates below
are derived from the stated auxiliary bound and convergent Euler inverse. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPrimaryDivisors (r : Eisenstein) : Finset Eisenstein :=
  (primaryElementBall (norm r)).filter (fun q => q ∣ r)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonOuterBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform bound for the actual shortened common-factor rows. The
roughness threshold enters their lengths, rather than a new hypothesis
about character cancellation. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def commonOuterCost (W : ℝ → ℂ) (C ε B Q A L D : ℝ) : ℝ :=
  (‖normProfileFourier W 0‖/9)*A + C*(B*Q^2*L^3/A)^ε*
    (max 1 (L/D)+A^(1/3:ℝ)*max 1 (L/D)+A^(2/3:ℝ)*(max 1 (L/D))^(2/3:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth product envelope equals one on the full sharp dyadic
interval. Thus the exact prime cutoff can be retained in the height integral
while every factorized row has a smooth product weight. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def primeProductWeights : UniformLogWeights (fun _ : Unit => primeProductEnvelope) :=
  uniformLogWeights_constant primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogNormCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual disjoint log-norm partition used in the integrated bilinear
estimate. Its finite fibers preserve both the sum and coefficient energy. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def logNormCell (J A : ℝ) (a : Eisenstein) : ℤ :=
  ⌊J*Real.log (norm a/A)⌋

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FarLogNormCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Far cells are the exact complement of the actual near-cell graph.
Every product in such a cell has the lower frequency bound needed for IBP. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def allLogNormCells (P S : Finset Eisenstein) (J A B : ℝ) : Finset (ℤ × ℤ) :=
  (P.image (logNormCell J A)).product (S.image (logNormCell J B))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GaussianSchwartz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual radial Gaussian as a Schwartz test function for lattice Poisson. -/
noncomputable section
open scoped SchwartzMap
namespace CubicFirstMoment

lemma radialGaussianSchwartz_traceFourier (a : ℝ) (ha : 0 < a) (w : ℂ) :
    traceFourier (radialGaussianSchwartz a ha) w =
      (Real.pi/a:ℝ) * (Real.exp (-4*Real.pi^2/a*Complex.normSq w):ℝ) := by
  have he : (radialGaussianSchwartz a ha : ℂ → ℂ) =
      fun z => Complex.exp (-(a:ℂ)*‖z‖^2) := by
    funext z
    rw [radialGaussianSchwartz_apply,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he,traceFourier_gaussian ha]
  rw [Complex.ofReal_exp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseEnvelopeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed product envelope in the sparse branch gives an actual
uniform family of inner weights on every fixed outer norm dyad. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

/-- A bounded logarithmic dilation preserves the given uniform smooth
weight bounds. Its support and all derivatives are derived explicitly. -/
def UniformLogWeights.logDilate {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) (D : ℝ) (hD : 0 ≤ D) :
    UniformLogWeights (fun z : γ × {s : ℝ // 0 < s ∧ |Real.log s| ≤ D} =>
      fun x => W z.1 (z.2*x)) := by
  refine ⟨?_,?_,?_,h.radius+D,add_nonneg h.radius_nonneg hD,?_,?_⟩
  · intro z
    exact (h.compact z.1).comp_homeomorph
      (Homeomorph.mulLeft₀ (z.2:ℝ) z.2.property.1.ne')
  · intro z x hx
    have hs : (z.2:ℝ)*x ∈ tsupport (W z.1) :=
      tsupport_comp_subset_preimage (W z.1) (f := fun x : ℝ => (z.2:ℝ)*x) (by fun_prop) hx
    have hp := h.positive z.1 hs
    change 0 < (z.2:ℝ)*x at hp
    exact (mul_pos_iff_of_pos_left z.2.property.1).mp hp
  · intro z
    exact (h.smooth z.1).comp (contDiff_const.mul contDiff_id)
  · intro z u hu
    have he : (fun v : ℝ => W z.1 ((z.2:ℝ)*Real.exp (-v))) =
        (fun v : ℝ => W z.1 (Real.exp (-v))) ∘ (fun v : ℝ => v-Real.log (z.2:ℝ)) := by
      ext v
      simp only [Function.comp_apply,scaled_exp_log z.2.property.1]
    rw [he] at hu
    have hs : u-Real.log (z.2:ℝ) ∈ tsupport (fun v : ℝ => W z.1 (Real.exp (-v))) :=
      tsupport_comp_subset_preimage _ (f := fun v : ℝ => v-Real.log (z.2:ℝ)) (by fun_prop) hu
    calc
      |u| = |(u-Real.log (z.2:ℝ))+Real.log (z.2:ℝ)| := by congr 1; ring
      _ ≤ |u-Real.log (z.2:ℝ)|+|Real.log (z.2:ℝ)| := abs_add_le _ _
      _ ≤ _ := add_le_add (h.support_bound z.1 _ hs) z.2.property.2
  · intro n
    obtain ⟨B,hB,hbound⟩ := h.derivative_bound n
    refine ⟨B,hB,?_⟩
    intro z u
    have he : (fun v : ℝ => W z.1 ((z.2:ℝ)*Real.exp (-v))) =
        (fun v : ℝ => W z.1 (Real.exp (-(v-Real.log (z.2:ℝ))))) := by
      ext v
      rw [scaled_exp_log z.2.property.1]
    rw [he]
    rw [iteratedFDeriv_comp_sub (f := fun v : ℝ => W z.1 (Real.exp (-v))) n (Real.log (z.2:ℝ)) u]
    exact hbound z.1 (u-Real.log (z.2:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogarithmicPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmically bounded height twists preserve the smooth weight
family used by the low-height Type-I theorem. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma linearHeightPhase_derivative (t x : ℝ) :
    HasDerivAt (linearHeightPhase t) (linearHeightPhase t x*((t:ℂ)*Complex.I)) x := by
  have h := (((hasDerivAt_id x).const_mul t).ofReal_comp.mul_const Complex.I).cexp
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · beta_reduce
    simp [linearHeightPhase]
  · simp [linearHeightPhase]

lemma linearHeightPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (linearHeightPhase t) =
      fun x => ((t:ℂ)*Complex.I)^n*linearHeightPhase t x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    rw [((linearHeightPhase_derivative t x).const_mul (((t:ℂ)*Complex.I)^n)).deriv]
    rw [pow_succ]
    ring

lemma linearHeightPhase_derivative_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (linearHeightPhase t) x‖ = |t|^n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,linearHeightPhase_iteratedDeriv]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one,linearHeightPhase,Complex.norm_exp_ofReal_mul_I]

def logarithmicPhaseWeight {γ : Type*} (Y : γ → ℝ) (W : γ → ℝ → ℂ) (d : ℕ)
    (i : logarithmicPhaseIndex Y d) (x : ℝ) : ℂ :=
  W i.val.1 x*mellinPhase i.val.2 x

def LogarithmicWeightFamily.phase {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (h : LogarithmicWeightFamily Y W) (d : ℕ) :
    LogarithmicWeightFamily (fun i : logarithmicPhaseIndex Y d => Y i.val.1)
      (logarithmicPhaseWeight Y W d) := by
  refine ⟨fun i => h.length_one i.val.1,
    fun i => phaseWeight_compact (h.compact i.val.1) i.val.2,
    fun i => phaseWeight_positive (h.positive i.val.1) i.val.2,
    fun i => phaseWeight_smooth (h.positive i.val.1) (h.smooth i.val.1) i.val.2,
    h.radius,h.radius_nonneg,?_,?_⟩
  · intro i u hu
    apply h.support_bound i.val.1 u
    apply tsupport_mul_subset_left hu
  · choose B A hB hb using h.derivative_bound
    intro n
    let E := d*n+∑ j ∈ Finset.range (n+1), A j
    let C := ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*B (n-j)
    have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hB _))
    refine ⟨C,E,hC,?_⟩
    intro i u
    let L := 1+Real.log (Y i.val.1)
    have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (h.length_one i.val.1)]
    have he : (fun v => logarithmicPhaseWeight Y W d i (Real.exp (-v))) =
        fun v => linearHeightPhase (-i.val.2) v*W i.val.1 (Real.exp (-v)) := by
      funext v
      dsimp [logarithmicPhaseWeight,linearHeightPhase,mellinPhase]
      rw [Real.log_exp]
      have hh : i.val.2*(-v) = (-i.val.2)*v := by ring
      rw [hh,mul_comm]
    rw [he]
    have hp : ContDiff ℝ ∞ (linearHeightPhase (-i.val.2)) := by
      unfold linearHeightPhase
      exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
        contDiff_const).cexp
    have hw : ContDiff ℝ ∞ (fun v => W i.val.1 (Real.exp (-v))) :=
      (h.smooth i.val.1).comp (by fun_prop)
    apply (norm_iteratedFDeriv_mul_le hp hw u (n := n) (mod_cast le_top)).trans
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*B (n-j)*L^E := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hBj := hB (n-j)
        have hphase : ‖iteratedFDeriv ℝ j (linearHeightPhase (-i.val.2)) u‖ ≤ L^(d*j) := by
          rw [linearHeightPhase_derivative_norm,abs_neg,pow_mul]
          exact pow_le_pow_left₀ (abs_nonneg _) i.property j
        have hA : A (n-j) ≤ ∑ k ∈ Finset.range (n+1), A k :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)))
        have hexp : d*j+A (n-j) ≤ E :=
          add_le_add (Nat.mul_le_mul_left d hjn) hA
        calc
          _ ≤ (n.choose j:ℝ)*L^(d*j)*(B (n-j)*L^(A (n-j))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hphase (Nat.cast_nonneg _)
            · exact hb (n-j) i.val.1 u
            · exact _root_.norm_nonneg _
            · positivity
          _ = (n.choose j:ℝ)*B (n-j)*L^(d*j+A (n-j)) := by rw [pow_add]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hexp) (by positivity)
      _ = C*L^E := by rw [Finset.sum_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeILogCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed logarithmic coefficient factors can be retained in the actual
weight family. This is the form used by short logarithmic convolutions. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def LogarithmicWeightFamily.logPower {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (h : LogarithmicWeightFamily Y W) (d : ℕ) :
    LogarithmicWeightFamily Y (logPowerWeight Y W d) := by
  have hsupp (i : γ) : Function.support (logPowerWeight Y W d i) ⊆ Function.support (W i) := by
    intro x hx hz
    exact hx (by simp [logPowerWeight,hz])
  refine ⟨h.length_one,fun i => (h.compact i).mono (hsupp i),
    fun i => (closure_mono (hsupp i)).trans (h.positive i),
    fun i => (h.smooth i).const_smul _,h.radius,h.radius_nonneg,?_,?_⟩
  · intro i u hu
    apply h.support_bound i u
    exact closure_mono (fun x hx => by
      intro hz
      exact hx (by simp [logPowerWeight,hz])) hu
  · intro n
    obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound n
    refine ⟨C,A+d,hC,?_⟩
    intro i u
    have hw : ContDiff ℝ ∞ (fun v => W i (Real.exp (-v))) := (h.smooth i).comp (by fun_prop)
    have hL : 0 ≤ 1+Real.log (Y i) := by linarith [Real.log_nonneg (h.length_one i)]
    change ‖iteratedFDeriv ℝ n (fun v => ((1+Real.log (Y i))^d:ℝ) •
      W i (Real.exp (-v))) u‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hw.of_le (by exact_mod_cast le_top)).contDiffAt),
      norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hL _)]
    calc
      _ ≤ (1+Real.log (Y i))^d*(C*(1+Real.log (Y i))^A) :=
        mul_le_mul_of_nonneg_left (hbound i u) (pow_nonneg hL _)
      _ = _ := by rw [pow_add]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIMixedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mixed-term weight from the corrected square. The factor
`(Na)^(-1/6)` is transferred to a fixed smooth test function and the
squarefree model is retained without removing mutual coprimality. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def UniformLogWeights.logarithmicWithLength {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) :
    LogarithmicWeightFamily (fun z : γ × {X : ℝ // 1 ≤ X} => (z.2:ℝ))
      (fun z x => W z.1 x) := by
  refine ⟨fun z => z.2.property,fun z => hW.compact z.1,
    fun z => hW.positive z.1,fun z => hW.smooth z.1,
    hW.radius,hW.radius_nonneg,fun z => hW.support_bound z.1,?_⟩
  intro n
  obtain ⟨C,hC,hbound⟩ := hW.derivative_bound n
  exact ⟨C,0,hC,fun z u => by simpa using hbound z.1 u⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single uniform smooth family for the actual distinguished-prime
weights in each large-row norm piece. Both scale ratios are capped only
after proving that the cap leaves the weight unchanged. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def compactDistinguishedSmoothWeights : UniformLogWeights
    (fun r : (Icc (0:ℝ) 2) ×ˢ (Icc (0:ℝ) 2) => distinguishedSmoothWeight r) :=
  uniformLogWeights_compactParameter _ (isCompact_Icc.prod isCompact_Icc)
    distinguishedSmoothWeight normPartitionWeight normPartitionWeight_compact
    normPartitionWeight_positive_support normPartitionWeight_smooth distinguishedSmoothWeight_contDiff
    (fun r _ => distinguishedSmoothWeight_support r)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimePNTProofSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational splitting and the literal primary Eisenstein primes. -/
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma isUnit_iff_normNat_eq_one (z : Eisenstein) : IsUnit z ↔ normNat z = 1 := by
  refine ⟨normNat_of_isUnit, fun h => isUnit_of_norm_eq_one ?_⟩
  rw [← normNat_cast, h, Nat.cast_one]

lemma prime_of_normNat_prime {z : Eisenstein} (hz : (normNat z).Prime) : Prime z := by
  apply irreducible_iff_prime.mp
  refine ⟨fun hu => hz.ne_one ((isUnit_iff_normNat_eq_one z).mp hu), ?_⟩
  intro a b hab
  have he : normNat a * normNat b = normNat z := by rw [← normNat_mul, ← hab]
  rcases Nat.prime_mul_iff.mp (he.symm ▸ hz) with h | h
  · exact Or.inr ((isUnit_iff_normNat_eq_one b).mpr h.2)
  · exact Or.inl ((isUnit_iff_normNat_eq_one a).mpr h.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMobiusGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation and level inversion matrices in the exact coordinates
used by the cubic theta Fourier and Mellin expansions. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaMobius_translation (t : ℂ) (p : ℂ × ℝ) :
    cubicThetaMobius (cubicThetaTranslationMatrix t) p = (p.1+t,p.2) := by
  apply Prod.ext <;>
    simp [cubicThetaMobius,cubicThetaTranslationMatrix,
      cubicThetaMobiusDenominator,cubicThetaMobiusNumerator]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive quadratic majorant for the initial cubic Eisenstein series.
This supplies actual convergence, rather than relying on formal reindexing. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaHeightConstant_pos {p : ℂ × ℝ} (hp : 0 < p.2) :
    0 < cubicThetaHeightConstant p := by
  have hz := Complex.normSq_nonneg p.1
  unfold cubicThetaHeightConstant
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate analyticity of every actual Eisenstein summand in the
positive upper half-space. -/
noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaCoordinateAnalytic_congr {F G : ℝ → ℝ → ℝ → ℂ}
    (hFG : ∀ x y v, 0<v → F x y v=G x y v) {x y v : ℝ} (hv : 0<v)
    (hG : CubicThetaCoordinateAnalytic G x y v) : CubicThetaCoordinateAnalytic F x y v := by
  refine ⟨hG.1.congr ?_,hG.2.1.congr ?_,hG.2.2.congr ?_⟩
  · exact Eventually.of_forall (fun t => (hFG t y v hv).symm)
  · exact Eventually.of_forall (fun t => (hFG x t v hv).symm)
  · filter_upwards [eventually_gt_nhds hv] with t ht
    exact (hFG x y t ht).symm

lemma cubicThetaCoordinateAnalytic_translated (s C : ℂ) (a b x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateAnalytic
      (fun u w t => C*cubicThetaCartesianKernel s (u+a) (w+b) t) x y v := by
  refine ⟨analyticAt_const.mul ?_,analyticAt_const.mul ?_,analyticAt_const.mul ?_⟩
  · exact (cubicThetaCartesian_x_analytic s (x+a) (y+b) hv).comp (f:=fun t : ℝ => t+a) (x:=x)
      (show AnalyticAt ℝ (fun t : ℝ => t+a) x by fun_prop)
  · exact (cubicThetaCartesian_y_analytic s (x+a) (y+b) hv).comp (f:=fun t : ℝ => t+b) (x:=y)
      (show AnalyticAt ℝ (fun t : ℝ => t+b) y by fun_prop)
  · exact cubicThetaCartesian_v_analytic s (x+a) (y+b) hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common relative bounds for the first and second coordinate jets.
They are preserved by scalar multiplication and horizontal translation. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaJetConstants_nonneg (s : ℂ) :
    0 ≤ cubicThetaFirstJetConstant s ∧ 0 ≤ cubicThetaSecondJetConstant s := by
  unfold cubicThetaFirstJetConstant cubicThetaSecondJetConstant
  constructor <;> positivity

lemma cubicThetaCartesian_jetBound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateJetBound (cubicThetaCartesianKernel s) s x y v := by
  have h1 : 2*‖s‖/v ≤ cubicThetaFirstJetConstant s/v := by
    apply div_le_div_of_nonneg_right _ hv.le
    unfold cubicThetaFirstJetConstant
    linarith [_root_.norm_nonneg s]
  have h2 : (2*‖s‖+4*‖s‖*‖s+1‖)/v^2 ≤ cubicThetaSecondJetConstant s/v^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg v)
    unfold cubicThetaSecondJetConstant
    linarith [_root_.norm_nonneg (s*(s-1)),_root_.norm_nonneg (4*s^2+2*s)]
  have h3 : (‖s*(s-1)‖+‖4*s^2+2*s‖+4*‖s‖*‖s+1‖)/v^2 ≤
      cubicThetaSecondJetConstant s/v^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg v)
    unfold cubicThetaSecondJetConstant
    linarith [_root_.norm_nonneg s]
  intro k
  cases k with
  | x => exact ⟨(cubicThetaCartesian_x_deriv_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h1 (_root_.norm_nonneg _)),
      (cubicThetaCartesian_x_second_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h2 (_root_.norm_nonneg _))⟩
  | y => exact ⟨(cubicThetaCartesian_y_deriv_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h1 (_root_.norm_nonneg _)),
      (cubicThetaCartesian_y_second_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h2 (_root_.norm_nonneg _))⟩
  | height => exact ⟨cubicThetaCartesian_v_deriv_bound s x y hv,
      (cubicThetaCartesian_v_second_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h3 (_root_.norm_nonneg _))⟩

lemma cubicThetaCoordinateJetBound_congr {F G : ℝ → ℝ → ℝ → ℂ}
    (hFG : ∀ x y v, 0<v → F x y v=G x y v) {s : ℂ} {x y v : ℝ} (hv : 0<v)
    (hG : CubicThetaCoordinateJetBound G s x y v) : CubicThetaCoordinateJetBound F s x y v := by
  intro k
  have he : cubicThetaAxisFunction F k x y v =ᶠ[𝓝 (cubicThetaCoordinateCenter k x y v)]
      cubicThetaAxisFunction G k x y v := by
    cases k with
    | x => exact Eventually.of_forall (fun t => hFG t y v hv)
    | y => exact Eventually.of_forall (fun t => hFG x t v hv)
    | height =>
      filter_upwards [eventually_gt_nhds hv] with t ht
      exact hFG x y t ht
  rw [he.deriv_eq,he.deriv.deriv_eq,hFG x y v hv]
  exact hG k

lemma cubicThetaCoordinateJetBound_translate {F : ℝ → ℝ → ℝ → ℂ} {s : ℂ}
    (C : ℂ) (a b x y v : ℝ) (hF : CubicThetaCoordinateJetBound F s (x+a) (y+b) v) :
    CubicThetaCoordinateJetBound (fun u w t => C*F (u+a) (w+b) t) s x y v := by
  intro k
  have hm (f : ℝ → ℂ) (t : ℝ) (h : ℝ) :
      ‖deriv (fun z => C*f (z+h)) t‖=‖C‖*‖deriv f (t+h)‖ ∧
      ‖deriv (deriv (fun z => C*f (z+h))) t‖=‖C‖*‖deriv (deriv f) (t+h)‖ := by
    simp [deriv_const_mul_field',cubicTheta_deriv_translate]
  have hmul (A B : ℝ) (h : A ≤ ‖F (x+a) (y+b) v‖*B) :
      ‖C‖*A ≤ ‖C*F (x+a) (y+b) v‖*B := by
    rw [norm_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left h (_root_.norm_nonneg _)
  cases k with
  | x =>
    have he := hm (fun t => F t (y+b) v) x a
    exact ⟨he.1.trans_le (hmul _ _ (hF .x).1),he.2.trans_le (hmul _ _ (hF .x).2)⟩
  | y =>
    have he := hm (fun t => F (x+a) t v) y b
    exact ⟨he.1.trans_le (hmul _ _ (hF .y).1),he.2.trans_le (hmul _ _ (hF .y).2)⟩
  | height =>
    have he := hm (fun t => F (x+a) (y+b) t) v 0
    simp only [add_zero] at he
    exact And.intro (he.1.trans_le (hmul _ _ (hF .height).1))
        (he.2.trans_le (hmul _ _ (hF .height).2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative bounds for all actual grid summands, with the zero row and
the inadmissible-pair extension included. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaHeightPower_jetBound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateJetBound (fun _ _ t => (t:ℂ)^s) s x y v := by
  have hn := cubicThetaJetConstants_nonneg s
  intro k
  cases k with
  | x =>
    simp only [cubicThetaAxisFunction,cubicThetaCoordinateCenter,deriv_const',deriv_const,norm_zero]
    exact ⟨mul_nonneg (_root_.norm_nonneg _) (div_nonneg hn.1 hv.le),
      mul_nonneg (_root_.norm_nonneg _) (div_nonneg hn.2 (sq_nonneg _))⟩
  | y =>
    simp only [cubicThetaAxisFunction,cubicThetaCoordinateCenter,deriv_const',deriv_const,norm_zero]
    exact ⟨mul_nonneg (_root_.norm_nonneg _) (div_nonneg hn.1 hv.le),
      mul_nonneg (_root_.norm_nonneg _) (div_nonneg hn.2 (sq_nonneg _))⟩
  | height =>
    change ‖deriv (fun t : ℝ => (t:ℂ)^s) v‖ ≤ _ ∧
      ‖deriv (deriv (fun t : ℝ => (t:ℂ)^s)) v‖ ≤ _
    rw [cubicThetaHeightPower_first_norm s hv,cubicThetaHeightPower_second_norm s hv]
    constructor
    · apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      apply div_le_div_of_nonneg_right _ hv.le
      unfold cubicThetaFirstJetConstant
      linarith [_root_.norm_nonneg s]
    · apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      apply div_le_div_of_nonneg_right _ (sq_nonneg v)
      unfold cubicThetaSecondJetConstant
      have hpos : 0 ≤ 4*‖s‖*‖s+1‖ := by positivity
      linarith [_root_.norm_nonneg s,_root_.norm_nonneg (4*s^2+2*s)]

lemma cubicThetaZero_jetBound (s : ℂ) (x y v : ℝ) :
    CubicThetaCoordinateJetBound (fun _ _ _ => (0:ℂ)) s x y v := by
  intro k
  cases k <;> simp [cubicThetaAxisFunction,cubicThetaCoordinateCenter]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientCharts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete local coordinate charts for the principal quotient, obtained
from the proved covering map and the open positive-height half-space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

lemma cubicThetaPointInclusion_target :
    cubicThetaPointInclusion.target={p : ℂ × ℝ | 0<p.2} := by
  exact positiveHeightOpen.openPartialHomeomorphSubtypeCoe_target _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSpatialDerivativeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A joint Frechet derivative bound for the actual Eisenstein summands.
The three proved coordinate bounds control the product-space operator norm. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaFDeriv_coordinates {F : ℂ × ℝ → ℂ} (x y v : ℝ)
    (hF : DifferentiableAt ℝ F (cubicThetaCartesianPoint x y v)) :
    (fderiv ℝ F (cubicThetaCartesianPoint x y v)) (1,0)=
      deriv (fun t => F (cubicThetaCartesianPoint t y v)) x ∧
    (fderiv ℝ F (cubicThetaCartesianPoint x y v)) (Complex.I,0)=
      deriv (fun t => F (cubicThetaCartesianPoint x t v)) y ∧
    (fderiv ℝ F (cubicThetaCartesianPoint x y v)) (0,1)=
      deriv (fun t => F (cubicThetaCartesianPoint x y t)) v := by
  have hx : HasDerivAt (fun t => cubicThetaCartesianPoint t y v) ((1:ℂ),(0:ℝ)) x := by
    simpa only [cubicThetaCartesianPoint,Complex.ofRealCLM_apply,Complex.ofReal_one] using
      ((Complex.ofRealCLM.hasDerivAt (x:=x)).add_const ((y:ℂ)*Complex.I)).prodMk (hasDerivAt_const x v)
  have hy : HasDerivAt (fun t => cubicThetaCartesianPoint x t v) (Complex.I,(0:ℝ)) y := by
    simpa only [cubicThetaCartesianPoint,Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using
      (((Complex.ofRealCLM.hasDerivAt (x:=y)).mul_const Complex.I).const_add (x:ℂ)).prodMk
        (hasDerivAt_const y v)
  have hv : HasDerivAt (fun t => cubicThetaCartesianPoint x y t) ((0:ℂ),(1:ℝ)) v := by
    exact (hasDerivAt_const v ((x:ℂ)+(y:ℂ)*Complex.I)).prodMk (hasDerivAt_id v)
  exact ⟨(hF.hasFDerivAt.comp_hasDerivAt x hx).deriv.symm,
    (hF.hasFDerivAt.comp_hasDerivAt y hy).deriv.symm,
    (hF.hasFDerivAt.comp_hasDerivAt v hv).deriv.symm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHermitianMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Determinant-one Hermitian coordinates and the invariant two-point
quantity underlying the hyperbolic metric. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaUnitHermitian (p : ℂ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (p.2:ℂ)⁻¹ • cubicThetaHermitian p

lemma cubicThetaUnitHermitian_mobius (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaUnitHermitian (cubicThetaMobius g p)=
      g.val*cubicThetaUnitHermitian p*g.valᴴ := by
  have hv : (p.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hd : (cubicThetaMobiusDenominator g p:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaMobius_denominator_pos g hp).ne'
  rw [cubicThetaUnitHermitian,cubicThetaHermitian_mobius g hp]
  change ((p.2/cubicThetaMobiusDenominator g p:ℝ):ℂ)⁻¹ •
    ((cubicThetaMobiusDenominator g p:ℂ)⁻¹ • cubicThetaMobiusQuadratic g p)=_
  rw [Complex.ofReal_div,smul_smul]
  have hs : ((p.2:ℂ)/(cubicThetaMobiusDenominator g p:ℂ))⁻¹*
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹=(p.2:ℂ)⁻¹ := by field_simp
  rw [hs]
  simp only [cubicThetaUnitHermitian,cubicThetaMobiusQuadratic,Matrix.mul_smul,Matrix.smul_mul]

lemma cubicThetaUnitHermitian_pair_det_invariant (g : SL(2,ℂ))
    {p q : ℂ × ℝ} (hp : 0<p.2) (hq : 0<q.2) :
    Matrix.det (cubicThetaUnitHermitian (cubicThetaMobius g p)+
      cubicThetaUnitHermitian (cubicThetaMobius g q))=
    Matrix.det (cubicThetaUnitHermitian p+cubicThetaUnitHermitian q) := by
  rw [cubicThetaUnitHermitian_mobius g hp,cubicThetaUnitHermitian_mobius g hq,
    ← Matrix.add_mul,← Matrix.mul_add,Matrix.det_mul,Matrix.det_mul,
    Matrix.det_conjTranspose,g.property]
  simp

lemma cubicThetaUnitHermitian_pair_det {p q : ℂ × ℝ} (hp : 0<p.2) (hq : 0<q.2) :
    Matrix.det (cubicThetaUnitHermitian p+cubicThetaUnitHermitian q)=
      (4:ℂ)+((Complex.normSq (p.1-q.1)+(p.2-q.2)^2)/(p.2*q.2):ℝ) := by
  have hv : (p.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hw : (q.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hq.ne'
  simp only [cubicThetaUnitHermitian,cubicThetaHermitian,cubicThetaRadius,
    Matrix.det_fin_two,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_sub,
    Complex.normSq_eq_conj_mul_self,map_sub,Complex.star_def]
  field_simp
  ring

lemma cubicThetaHyperbolicChord_invariant (g : SL(2,ℂ))
    {p q : ℂ × ℝ} (hp : 0<p.2) (hq : 0<q.2) :
    cubicThetaHyperbolicChord (cubicThetaMobius g p) (cubicThetaMobius g q)=
      cubicThetaHyperbolicChord p q := by
  have h := cubicThetaUnitHermitian_pair_det_invariant g hp hq
  rw [cubicThetaUnitHermitian_pair_det (cubicThetaMobius_height_pos g hp)
    (cubicThetaMobius_height_pos g hq),cubicThetaUnitHermitian_pair_det hp hq] at h
  apply Complex.ofReal_injective
  exact add_left_cancel h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMetricScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-point metric identity gives exact scaling of Euclidean squared
lengths under the actual hyperbolic action. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaRadius_smul (t : ℝ) (u : ℂ × ℝ) :
    cubicThetaRadius (t • u)=t^2*cubicThetaRadius u := by
  change Complex.normSq ((t:ℂ)*u.1)+(t*u.2)^2=t^2*(Complex.normSq u.1+u.2^2)
  rw [Complex.normSq_mul,Complex.normSq_ofReal]
  ring

lemma cubicThetaRadius_continuous : Continuous cubicThetaRadius := by
  unfold cubicThetaRadius
  fun_prop

lemma cubicThetaMobius_secant_scale (g : SL(2,ℂ)) {p u : ℂ × ℝ}
    (hp : 0<p.2) {t : ℝ} (ht : t≠0) (hq : 0<(p+t • u).2) :
    cubicThetaRadius (t⁻¹ • (cubicThetaMobius g (p+t • u)-cubicThetaMobius g p))*
        ((p+t • u).2*p.2)=
      cubicThetaRadius u*((cubicThetaMobius g (p+t • u)).2*(cubicThetaMobius g p).2) := by
  have h := cubicThetaHyperbolicChord_invariant g hq hp
  change cubicThetaRadius (cubicThetaMobius g (p+t • u)-cubicThetaMobius g p)/
    ((cubicThetaMobius g (p+t • u)).2*(cubicThetaMobius g p).2)=
    cubicThetaRadius (p+t • u-p)/((p+t • u).2*p.2) at h
  have hd := mul_ne_zero (cubicThetaMobius_height_pos g hq).ne'
    (cubicThetaMobius_height_pos g hp).ne'
  have hd' := mul_ne_zero hq.ne' hp.ne'
  rw [div_eq_div_iff hd hd'] at h
  have he : p+t • u-p=t • u := by abel
  rw [he,cubicThetaRadius_smul] at h
  rw [cubicThetaRadius_smul]
  field_simp
  nlinarith [h]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMetricDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact hyperbolic metric scaling of the derivative follows from the
proved two-point identity, by taking real directional secants. -/
noncomputable section
open Filter Topology
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaMobius_derivative_scale (g : SL(2,ℂ)) {p : ℂ × ℝ}
    (hp : 0<p.2) (u : ℂ × ℝ) :
    cubicThetaRadius (fderiv ℝ (cubicThetaMobius g) p u)*p.2^2=
      cubicThetaRadius u*(cubicThetaMobius g p).2^2 := by
  let path : ℝ → ℂ × ℝ := fun t => p+t • u
  have hpath : HasDerivAt path u 0 := by
    change HasDerivAt (fun t : ℝ => p+t • u) u 0
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add p
  have hf := (cubicThetaMobius_contDiffAt g hp).differentiableAt (by norm_num)
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp [path])
  have hsec : Tendsto (fun t : ℝ => t⁻¹ • (cubicThetaMobius g (path t)-cubicThetaMobius g p))
      (𝓝[≠] 0) (𝓝 (fderiv ℝ (cubicThetaMobius g) p u)) := by
    simpa only [Function.comp_apply,zero_add,path,zero_smul,add_zero] using hd.tendsto_slope_zero
  have hheight : Tendsto (fun t => (path t).2) (𝓝[≠] (0:ℝ)) (𝓝 p.2) := by
    have hh := hpath.continuousAt.snd.tendsto
    simp only [path,zero_smul,add_zero] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have hheight' : Tendsto (fun t => (cubicThetaMobius g (path t)).2)
      (𝓝[≠] (0:ℝ)) (𝓝 (cubicThetaMobius g p).2) := by
    have hh := hd.continuousAt.snd.tendsto
    simp only [Function.comp_apply,path,zero_smul,add_zero] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have hleft := (cubicThetaRadius_continuous.continuousAt.tendsto.comp hsec).mul
    (hheight.mul (tendsto_const_nhds (x:=p.2)))
  have hright := (tendsto_const_nhds (x:=cubicThetaRadius u)).mul
    (hheight'.mul (tendsto_const_nhds (x:=(cubicThetaMobius g p).2)))
  have hpos : ∀ᶠ t in 𝓝 (0:ℝ), 0<(path t).2 := by
    exact hpath.continuousAt.snd.tendsto.eventually
      (Ioi_mem_nhds (by simpa only [path,zero_smul,add_zero] using hp))
  have he : (fun t : ℝ => cubicThetaRadius (t⁻¹ •
        (cubicThetaMobius g (path t)-cubicThetaMobius g p))*((path t).2*p.2)) =ᶠ[𝓝[≠] 0]
      (fun t => cubicThetaRadius u*((cubicThetaMobius g (path t)).2*(cubicThetaMobius g p).2)) := by
    filter_upwards [hpos.filter_mono inf_le_left,self_mem_nhdsWithin] with t ht ht0
    exact cubicThetaMobius_secant_scale g hp ht0 ht
  simpa only [pow_two] using tendsto_nhds_unique_of_eventuallyEq hleft hright he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Mobius Jacobian has absolute determinant equal to the cube
of the height ratio. Thus the hyperbolic volume density is invariant. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma tangent_norm_sq (u : TangentL2) : ‖u‖^2=cubicThetaRadius (tangentCoordinates u) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [cubicThetaRadius,tangentCoordinates,WithLp.coe_linearEquiv,Complex.normSq_eq_norm_sq,
    Real.norm_eq_abs,sq_abs]
  rfl

lemma cubicThetaMobius_abs_det (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    |(fderiv ℝ (cubicThetaMobius g) p).toLinearMap.det|=
      ((cubicThetaMobius g p).2/p.2)^3 := by
  let L := (fderiv ℝ (cubicThetaMobius g) p).toLinearMap
  let A : TangentL2 →ₗ[ℝ] TangentL2 :=
    tangentCoordinates.symm.toLinearMap.comp (L.comp tangentCoordinates.toLinearMap)
  let k := (cubicThetaMobius g p).2/p.2
  have hk : 0<k := div_pos (cubicThetaMobius_height_pos g hp) hp
  have hnorm (u : TangentL2) : ‖A u‖=k*‖u‖ := by
    have hs := cubicThetaMobius_derivative_scale g hp (tangentCoordinates u)
    have hA : cubicThetaRadius (fderiv ℝ (cubicThetaMobius g) p (tangentCoordinates u))=‖A u‖^2 := by
      rw [tangent_norm_sq]
      simp only [A,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,L]
      rfl
    rw [hA,← tangent_norm_sq] at hs
    have he : (‖A u‖*p.2)^2=(‖u‖*(cubicThetaMobius g p).2)^2 := by nlinarith [hs]
    have he' := (sq_eq_sq₀ (mul_nonneg (_root_.norm_nonneg (A u)) hp.le)
      (mul_nonneg (_root_.norm_nonneg u) (cubicThetaMobius_height_pos g hp).le)).mp he
    calc
      ‖A u‖=(‖u‖*(cubicThetaMobius g p).2)/p.2 := (eq_div_iff hp.ne').mpr he'
      _ = k*‖u‖ := by dsimp [k]; ring
  let J : TangentL2 →ₗᵢ[ℝ] TangentL2 :=
    { toLinearMap := k⁻¹ • A
      norm_map' := by
        intro u
        change ‖k⁻¹ • A u‖=‖u‖
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk),hnorm]
        field_simp }
  have hJ := J.normDet_eq_one
  change (k⁻¹ • A).normDet=1 at hJ
  rw [LinearMap.normDet_smul,tangent_finrank,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk)] at hJ
  have hA : A.normDet=k^3 := by
    calc
      A.normDet=(k^3*(k⁻¹)^3)*A.normDet := by field_simp
      _ = k^3 := by rw [mul_assoc,hJ,mul_one]
  rw [LinearMap.normDet_eq_abs_det] at hA
  have hdet : A.det=L.det := LinearMap.det_conj L tangentCoordinates.symm
  rw [hdet] at hA
  exact hA

lemma cubicThetaMobius_volume_density (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    |(fderiv ℝ (cubicThetaMobius g) p).toLinearMap.det|/
      (cubicThetaMobius g p).2^3=1/p.2^3 := by
  rw [cubicThetaMobius_abs_det g hp]
  field_simp [(cubicThetaMobius_height_pos g hp).ne',hp.ne']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHyperbolicIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change of variables for the actual hyperbolic volume density v^-3.
This is the chart-independent integral used for the automorphic energy. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaMobius_injOn (g : SL(2,ℂ)) :
    Set.InjOn (cubicThetaMobius g) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp q hq he
  have h := congrArg (cubicThetaMobius g⁻¹) he
  rw [cubicThetaMobius_comp _ _ hp,cubicThetaMobius_comp _ _ hq] at h
  simpa only [inv_mul_cancel,cubicThetaMobius_one] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHyperbolicMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual invariant hyperbolic measure on positive-height points.
Its density is v^-3, and arithmetic invariance follows from the proved
Jacobian, not from an assumed invariant measure. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ENNReal
namespace CubicFirstMoment

lemma cubicThetaHyperbolicDensity_transform (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    ENNReal.ofReal |(fderiv ℝ (cubicThetaMobius g) p).toLinearMap.det| *
      cubicThetaHyperbolicDensity (cubicThetaMobius g p)=cubicThetaHyperbolicDensity p := by
  unfold cubicThetaHyperbolicDensity
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  apply congrArg ENNReal.ofReal
  simpa only [div_eq_mul_inv,one_mul] using cubicThetaMobius_volume_density g hp

attribute [local instance] OAI.CubicFirstMoment.cubicThetaHyperbolicMeasure_volumeHaar
lemma cubicThetaHyperbolic_lintegral_change (g : SL(2,ℂ)) {S : Set (ℂ × ℝ)}
    (hS : MeasurableSet S) (hpos : ∀ p∈S,0<p.2) (F : ℂ × ℝ → ℝ≥0∞) :
    (∫⁻ p in cubicThetaMobius g '' S, cubicThetaHyperbolicDensity p*F p)=
      ∫⁻ p in S, cubicThetaHyperbolicDensity p*F (cubicThetaMobius g p) := by
  have hD : ∀ p∈S, HasFDerivWithinAt (cubicThetaMobius g)
      (fderiv ℝ (cubicThetaMobius g) p) S p := by
    intro p hp
    exact ((cubicThetaMobius_contDiffAt g (hpos p hp)).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hD
    ((cubicThetaMobius_injOn g).mono hpos)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hS] with p hp
  rw [← mul_assoc,cubicThetaHyperbolicDensity_transform g (hpos p hp)]

lemma cubicThetaHyperbolicMeasure_image (g : SL(2,ℂ)) {S : Set (ℂ × ℝ)}
    (hS : MeasurableSet S) (hpos : ∀ p∈S,0<p.2) :
    cubicThetaHyperbolicMeasure (cubicThetaMobius g '' S)=cubicThetaHyperbolicMeasure S := by
  unfold cubicThetaHyperbolicMeasure
  rw [withDensity_apply',withDensity_apply']
  simpa only [mul_one] using cubicThetaHyperbolic_lintegral_change g hS hpos (fun _ => 1)

lemma cubicThetaPointInclusion_measurableEmbedding :
    MeasurableEmbedding cubicThetaPointCoordinates := by
  apply Topology.IsOpenEmbedding.measurableEmbedding
  change Topology.IsOpenEmbedding (Subtype.val : {p : ℂ × ℝ // 0<p.2} → ℂ × ℝ)
  exact (isOpen_lt continuous_const continuous_snd).isOpenEmbedding_subtypeVal

lemma cubicThetaPointMeasure_apply {S : Set CubicThetaPoint} (hS : MeasurableSet S) :
    cubicThetaPointMeasure S=cubicThetaHyperbolicMeasure (cubicThetaPointCoordinates '' S) :=
  Measure.comap_apply _ cubicThetaPointInclusion_measurableEmbedding.injective
    (fun _ hs => cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hs) _ hS

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointMeasureLocallyFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hyperbolic measure is finite on each compact positive-height set;
the singularity at height zero stays outside every such compact set. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPointCoordinates_continuous : Continuous cubicThetaPointCoordinates :=
  continuous_subtype_val

lemma cubicThetaPointMeasure_compact {K : Set CubicThetaPoint} (hK : IsCompact K) :
    cubicThetaPointMeasure K<⊤ := by
  let L := cubicThetaPointCoordinates '' K
  have hL : IsCompact L := hK.image cubicThetaPointCoordinates_continuous
  have hpos : ∀ p∈L,0<p.2 := by
    rintro p ⟨q,_,rfl⟩
    exact q.property
  have hc : ContinuousOn (fun p : ℂ × ℝ => (p.2^3)⁻¹) L := by
    intro p hp
    exact ((continuous_snd.continuousAt.pow 3).inv₀ (pow_ne_zero 3 (hpos p hp).ne')).continuousWithinAt
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn hc
  rw [cubicThetaPointMeasure_apply hK.isClosed.measurableSet]
  change cubicThetaHyperbolicMeasure L<⊤
  unfold cubicThetaHyperbolicMeasure
  rw [withDensity_apply']
  calc
    _ ≤ ∫⁻ _ in L, ENNReal.ofReal C := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hL.isClosed.measurableSet] with p hp
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self _).trans (hC p hp)
    _ = ENNReal.ofReal C*volume L := by simp only [lintegral_const,Measure.restrict_apply_univ]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL.measure_lt_top

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaChartSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact Euclidean chart profile gives a genuine compact smooth
section. On its covering sheet the periodization is exactly the seed. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveSeed_compact {φ : ℂ × ℝ → ℂ}
    (hc : HasCompactSupport φ) (hpos : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) :
    HasCompactSupport (fun p : CubicThetaPoint => φ p.val) := by
  have hinc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hK := hc.image_of_continuousOn (hinc.mono hpos)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro p hp
  refine ⟨p.val,subset_tsupport φ hp,?_⟩
  exact cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTangentIsometry
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized differential of an actual Mobius transformation is
an orthogonal automorphism of the three-dimensional real tangent space. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaTangent_norm_sq (u : CubicThetaTangent) :
    ‖u‖^2=cubicThetaRadius (cubicThetaTangentCoordinates u) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [cubicThetaRadius,cubicThetaTangentCoordinates,
    Complex.normSq_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  rfl

def cubicThetaTangentDerivative (g : SL(2,ℂ)) (p : ℂ × ℝ) :
    CubicThetaTangent →L[ℝ] CubicThetaTangent :=
  cubicThetaTangentCoordinates.symm.toContinuousLinearMap.comp
    ((fderiv ℝ (cubicThetaMobius g) p).comp
      cubicThetaTangentCoordinates.toContinuousLinearMap)

lemma cubicThetaTangentDerivative_norm (g : SL(2,ℂ)) {p : ℂ × ℝ}
    (hp : 0<p.2) (u : CubicThetaTangent) :
    ‖cubicThetaTangentDerivative g p u‖=
      ((cubicThetaMobius g p).2/p.2)*‖u‖ := by
  have hs := cubicThetaMobius_derivative_scale g hp (cubicThetaTangentCoordinates u)
  have hA : cubicThetaRadius (fderiv ℝ (cubicThetaMobius g) p
      (cubicThetaTangentCoordinates u))=‖cubicThetaTangentDerivative g p u‖^2 := by
    rw [cubicThetaTangent_norm_sq]
    simp only [cubicThetaTangentDerivative,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
  rw [hA,← cubicThetaTangent_norm_sq] at hs
  have he : (‖cubicThetaTangentDerivative g p u‖*p.2)^2=
      (‖u‖*(cubicThetaMobius g p).2)^2 := by nlinarith [hs]
  have he' := (sq_eq_sq₀
    (mul_nonneg (_root_.norm_nonneg _) hp.le)
    (mul_nonneg (_root_.norm_nonneg _) (cubicThetaMobius_height_pos g hp).le)).mp he
  calc
    _ = (‖u‖*(cubicThetaMobius g p).2)/p.2 := (eq_div_iff hp.ne').mpr he'
    _ = _ := by ring

def cubicThetaTangentIsometry (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    CubicThetaTangent ≃ₗᵢ[ℝ] CubicThetaTangent := by
  let k := (cubicThetaMobius g p).2/p.2
  have hk : 0<k := div_pos (cubicThetaMobius_height_pos g hp) hp
  let J : CubicThetaTangent →ₗᵢ[ℝ] CubicThetaTangent :=
    { toLinearMap := k⁻¹ • (cubicThetaTangentDerivative g p).toLinearMap
      norm_map' := by
        intro u
        change ‖k⁻¹ • cubicThetaTangentDerivative g p u‖=‖u‖
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk),
          cubicThetaTangentDerivative_norm g hp]
        change k⁻¹*(k*‖u‖)=‖u‖
        rw [← mul_assoc,inv_mul_cancel₀ hk.ne',one_mul] }
  exact LinearIsometryEquiv.ofSurjective J
    (LinearMap.surjective_of_injective J.injective)

lemma cubicThetaTangentDerivative_eq (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2)
    (u : CubicThetaTangent) :
    cubicThetaTangentDerivative g p u=
      ((cubicThetaMobius g p).2/p.2) • cubicThetaTangentIsometry g hp u := by
  change _= ((cubicThetaMobius g p).2/p.2) •
    (((cubicThetaMobius g p).2/p.2)⁻¹ • cubicThetaTangentDerivative g p u)
  rw [smul_smul,mul_inv_cancel₀
    (div_pos (cubicThetaMobius_height_pos g hp) hp).ne',one_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTangentEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squared differential norm is independent of the orthonormal
tangent frame. This is the complex-valued Dirichlet energy, expressed
as the sum of the real and imaginary dual norms. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_isometry (L : CubicThetaTangent →L[ℝ] ℂ)
    (J : CubicThetaTangent ≃ₗᵢ[ℝ] CubicThetaTangent) :
    cubicThetaTangentEnergy (L.comp J.toContinuousLinearEquiv.toContinuousLinearMap)=
      cubicThetaTangentEnergy L := by
  change (∑ i, ‖L ((cubicThetaTangentBasis.map J) i)‖^2)=_
  rw [cubicThetaTangentEnergy_basis]
  exact (cubicThetaTangentEnergy_basis cubicThetaTangentBasis L).symm

lemma cubicThetaTangentEnergy_real_smul (r : ℝ) (L : CubicThetaTangent →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (r • L)=r^2*cubicThetaTangentEnergy L := by
  simp only [cubicThetaTangentEnergy,smul_apply,norm_smul,
    mul_pow,Real.norm_eq_abs,sq_abs,Finset.mul_sum]

lemma cubicThetaTangentEnergy_complex_smul (c : ℂ) (L : CubicThetaTangent →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (c • L)=‖c‖^2*cubicThetaTangentEnergy L := by
  simp only [cubicThetaTangentEnergy,smul_apply,norm_smul,
    mul_pow,Finset.mul_sum]

lemma cubicThetaTangentEnergy_derivative (L : CubicThetaTangent →L[ℝ] ℂ)
    (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaTangentEnergy (L.comp (cubicThetaTangentDerivative g p))=
      ((cubicThetaMobius g p).2/p.2)^2*cubicThetaTangentEnergy L := by
  have he : L.comp (cubicThetaTangentDerivative g p)=
      ((cubicThetaMobius g p).2/p.2) •
        (L.comp (cubicThetaTangentIsometry g hp).toContinuousLinearEquiv.toContinuousLinearMap) := by
    ext u
    simp only [ContinuousLinearMap.comp_apply,smul_apply,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [cubicThetaTangentDerivative_eq g hp,L.map_smul]
  rw [he,cubicThetaTangentEnergy_real_smul,cubicThetaTangentEnergy_isometry]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticCuspEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of the arithmetic energy to a cusp, followed by
the operator-norm bound for its genuine joint derivative. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaTangentCoordinates_norm_le (u : CubicThetaTangent) :
    ‖cubicThetaTangentCoordinates u‖≤‖u‖ := by
  rw [Prod.norm_def]
  exact max_le (WithLp.norm_fst_le ℂ u) (WithLp.norm_snd_le ℂ u)

lemma cubicThetaTangentEnergy_coordinate_bound (L : (ℂ × ℝ) →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (L.comp cubicThetaTangentCoordinates.toContinuousLinearMap)≤
      (Module.finrank ℝ CubicThetaTangent:ℝ)*‖L‖^2 := by
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ CubicThetaTangent), ‖L‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := L.le_opNorm (cubicThetaTangentCoordinates (cubicThetaTangentBasis i))
      have hu := cubicThetaTangentCoordinates_norm_le (cubicThetaTangentBasis i)
      rw [cubicThetaTangentBasis.norm_eq_one] at hu
      have hb : ‖L (cubicThetaTangentCoordinates (cubicThetaTangentBasis i))‖≤‖L‖ :=
        h.trans ((mul_le_mul_of_nonneg_left hu (_root_.norm_nonneg L)).trans_eq (mul_one _))
      exact (sq_le_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mpr hb
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAxisDifferentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate derivatives are actual directional derivatives on
complex-horizontal and real-height space. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

def cubicThetaAxisVector : CubicThetaAxis → ℂ × ℝ
  | .x => (1,0)
  | .y => (Complex.I,0)
  | .height => (0,1)

def cubicThetaAxisFirst (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  deriv (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
    (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)

lemma cubicThetaCartesianPoint_self (p : ℂ × ℝ) :
    cubicThetaCartesianPoint p.1.re p.1.im p.2=p := by
  apply Prod.ext
  · exact Complex.re_add_im p.1
  · rfl

lemma cubicThetaAxisFirst_eq_fderiv (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    {p : ℂ × ℝ} (hf : DifferentiableAt ℝ f p) :
    cubicThetaAxisFirst k f p=fderiv ℝ f p (cubicThetaAxisVector k) := by
  have hp := cubicThetaCartesianPoint_self p
  have hfc : DifferentiableAt ℝ f (cubicThetaCartesianPoint p.1.re p.1.im p.2) := hp.symm ▸ hf
  have h := cubicThetaFDeriv_coordinates p.1.re p.1.im p.2 hfc
  rw [hp] at h
  cases k
  · exact h.1.symm
  · exact h.2.1.symm
  · exact h.2.2.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A half-open three-Eisenstein period cell gives a genuinely injective
high cusp strip in the arithmetic quotient. Boundary points retain their
unique representatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaPoint_polish : PolishSpace CubicThetaPoint :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ × ℝ | 0<p.2}).polishSpace

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Heights of all representatives above a compact quotient set are
uniformly bounded. The arithmetic denominator bound is essential here:
a nonparabolic transformation sends height v to at most 1/v. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPointHeight (p : CubicThetaPoint) : ℝ := (cubicThetaPointCoordinates p).2

lemma cubicThetaPointHeight_pos (p : CubicThetaPoint) : 0 < cubicThetaPointHeight p := p.property

lemma cubicThetaPointHeight_continuous : Continuous cubicThetaPointHeight := by
  have h : Continuous cubicThetaPointCoordinates := continuous_subtype_val
  exact continuous_snd.comp h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted coordinate integration for the actual hyperbolic measure.
This identifies the v^-3 density appearing in the local energy graph. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointCoordinates_map_restrict {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) :
    (cubicThetaPointMeasure.restrict S).map cubicThetaPointCoordinates=
      cubicThetaHyperbolicMeasure.restrict (cubicThetaPointCoordinates '' S) := by
  ext B hB
  rw [Measure.map_apply cubicThetaPointInclusion_measurableEmbedding.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaPointInclusion_measurableEmbedding.measurable),
    cubicThetaPointMeasure_apply ((hB.preimage
      cubicThetaPointInclusion_measurableEmbedding.measurable).inter hS),
    Measure.restrict_apply hB,Set.image_preimage_inter]

lemma cubicThetaPointIntegral_coordinates {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (f : ℂ × ℝ → ℝ) :
    (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ y in cubicThetaPointCoordinates '' S, f y ∂cubicThetaHyperbolicMeasure := by
  rw [← cubicThetaPointCoordinates_map_restrict hS]
  exact (cubicThetaPointInclusion_measurableEmbedding.integral_map f).symm

lemma cubicThetaHyperbolicDensity_measurable : Measurable cubicThetaHyperbolicDensity :=
  ((measurable_snd.pow_const 3).inv).ennreal_ofReal

lemma cubicThetaPointIntegral_density {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (f : ℂ × ℝ → ℝ) :
    (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ y in cubicThetaPointCoordinates '' S, f y/y.2^3 := by
  rw [cubicThetaPointIntegral_coordinates hS]
  have hT := cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS
  rw [cubicThetaHyperbolicMeasure,setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    cubicThetaHyperbolicDensity_measurable.aemeasurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ hT]
  apply setIntegral_congr_fun hT
  rintro y ⟨p,hp,rfl⟩
  have hv : 0<(cubicThetaPointCoordinates p).2 := p.property
  simp only [cubicThetaHyperbolicDensity,ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hv.le 3)),
    smul_eq_mul,div_eq_mul_inv]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact coordinate functions give actual automorphic sections.
Their C1 regularity follows from the locally finite arithmetic sum. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaCoordinateSeed (g : ℂ × ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2}) :
    C_c(CubicThetaPoint,ℂ) :=
  ⟨⟨fun p => g p.val,hg.comp continuous_subtype_val⟩,cubicThetaPositiveSeed_compact hc hp⟩

lemma cubicThetaCoordinateSeed_coordinates (g : ℂ × ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2})
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaCoordinateSeed g hg hc hp (cubicThetaPointInclusion.symm y)=g y := by
  change g (cubicThetaPointInclusion.symm y).val=g y
  exact congrArg g (cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateSectionSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact support and differential identities on an injective
covering sheet for periodized coordinate functions. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaCoordinateSeed_support (g : ℂ × ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2}) :
    tsupport (cubicThetaCoordinateSeed g hg hc hp)⊆
      cubicThetaPointInclusion.symm '' tsupport g := by
  have hi : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hcompact := hc.image_of_continuousOn (hi.mono hp)
  apply closure_minimal _ hcompact.isClosed
  intro p hps
  refine ⟨p.val,subset_tsupport g hps,?_⟩
  exact cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative product estimates for the compact core cutoffs.
The coefficient is compactly supported, so its supremum is finite. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_add_le (L M : CubicThetaTangent →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (L+M)≤2*cubicThetaTangentEnergy L+2*cubicThetaTangentEnergy M := by
  unfold cubicThetaTangentEnergy
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simp only [add_apply]
  have ht := norm_add_le (L (cubicThetaTangentBasis i)) (M (cubicThetaTangentBasis i))
  have hs := mul_self_le_mul_self (_root_.norm_nonneg _) ht
  nlinarith [sq_nonneg (‖L (cubicThetaTangentBasis i)‖-‖M (cubicThetaTangentBasis i)‖)]

lemma cubicThetaFunctionEnergy_mul {f g : ℂ × ℝ → ℂ} {y : ℂ × ℝ}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    cubicThetaFunctionEnergy (f*g) y≤
      2*‖f y‖^2*cubicThetaFunctionEnergy g y+2*‖g y‖^2*cubicThetaFunctionEnergy f y := by
  have he : ((fderiv ℝ (f*g) y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)=
      f y • ((fderiv ℝ g y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)+
        g y • ((fderiv ℝ f y).comp cubicThetaTangentCoordinates.toContinuousLinearMap) := by
    rw [fderiv_mul hf hg]
    ext u
    simp only [ContinuousLinearMap.comp_apply,add_apply,smul_apply]
  unfold cubicThetaFunctionEnergy
  rw [he]
  exact (cubicThetaTangentEnergy_add_le _ _).trans_eq (by
    rw [cubicThetaTangentEnergy_complex_smul,cubicThetaTangentEnergy_complex_smul]
    ring)

def cubicThetaCutoffEnergyCoefficient (φ : ℂ × ℝ → ℂ) (y : ℂ × ℝ) : ℝ :=
  2*‖φ y‖^2+2*y.2^2*cubicThetaFunctionEnergy φ y

lemma cubicThetaLocalEnergyJet_cutoff_le {φ f : ℂ × ℝ → ℂ} {y : ℂ × ℝ}
    (hy : 0<y.2) (hφ : DifferentiableAt ℝ φ y) (hf : DifferentiableAt ℝ f y) :
    ‖cubicThetaLocalEnergyJet (φ*f) y‖^2≤
      cubicThetaCutoffEnergyCoefficient φ y*‖cubicThetaLocalEnergyJet f y‖^2 := by
  rw [cubicThetaLocalEnergyJet_density _ hy,cubicThetaLocalEnergyJet_density _ hy,
    ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (pow_pos hy 3)).mpr
  have he := cubicThetaFunctionEnergy_mul hφ hf
  have hEφ := cubicThetaTangentEnergy_nonneg
    ((fderiv ℝ φ y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)
  have hEf := cubicThetaTangentEnergy_nonneg
    ((fderiv ℝ f y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)
  change 0 ≤ cubicThetaFunctionEnergy φ y at hEφ
  change 0 ≤ cubicThetaFunctionEnergy f y at hEf
  have hmul := mul_le_mul_of_nonneg_left he (sq_nonneg y.2)
  simp only [Pi.mul_apply,norm_mul,mul_pow]
  unfold cubicThetaCutoffEnergyCoefficient
  nlinarith [mul_nonneg (sq_nonneg ‖φ y‖) (sq_nonneg ‖f y‖),
    mul_nonneg (sq_nonneg y.2) (mul_nonneg hEφ hEf)]

lemma cubicThetaCutoffEnergyCoefficient_bounded {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ∃ C≥0, ∀ y, cubicThetaCutoffEnergyCoefficient φ y≤C := by
  have hcont : Continuous (cubicThetaCutoffEnergyCoefficient φ) :=
    (continuous_const.mul (hφ.continuous.norm.pow 2)).add
      ((continuous_const.mul (continuous_snd.pow 2)).mul (cubicThetaFunctionEnergy_continuous hφ))
  have hcompact : HasCompactSupport (cubicThetaCutoffEnergyCoefficient φ) :=
    ((hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)).mul_left).add
      ((cubicThetaFunctionEnergy_compact hc).mul_left)
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuous hcont
  refine ⟨max C 0,le_max_right _ _,fun y => ?_⟩
  exact (le_abs_self _).trans ((hC y).trans (le_max_left _ _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateEnergyBound
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform C1 control on one compact positive-height chart controls
the exact norm of the periodized value-gradient data. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCoordinateEnergy_density_bound {g : ℂ × ℝ → ℂ} {ε : ℝ}
    (_hε : 0≤ε) (hv : ∀ y, ‖g y‖≤ε) (hd : ∀ y, ‖fderiv ℝ g y‖≤ε)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3≤
      ((y.2^3)⁻¹+(Module.finrank ℝ CubicThetaTangent:ℝ)/y.2)*ε^2 := by
  have hv2 : ‖g y‖^2≤ε^2 := pow_le_pow_left₀ (_root_.norm_nonneg _) (hv y) 2
  have hd2 : ‖fderiv ℝ g y‖^2≤ε^2 := pow_le_pow_left₀ (_root_.norm_nonneg _) (hd y) 2
  have he : cubicThetaFunctionEnergy g y≤(Module.finrank ℝ CubicThetaTangent:ℝ)*ε^2 :=
    (cubicThetaTangentEnergy_coordinate_bound (fderiv ℝ g y)).trans
      (mul_le_mul_of_nonneg_left hd2 (Nat.cast_nonneg _))
  calc
    _ = ‖g y‖^2/y.2^3+cubicThetaFunctionEnergy g y/y.2 := by field_simp [hy.ne']
    _ ≤ ε^2/y.2^3+((Module.finrank ℝ CubicThetaTangent:ℝ)*ε^2)/y.2 :=
      add_le_add (div_le_div_of_nonneg_right hv2 (pow_nonneg hy.le 3))
        (div_le_div_of_nonneg_right he hy.le)
    _ = _ := by ring

lemma cubicThetaCoordinateEnergy_integral_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ (g : ℂ × ℝ → ℂ), ContDiff ℝ 1 g → ∀ ε : ℝ, 0≤ε →
      (∀ y, ‖g y‖≤ε) → (∀ y, ‖fderiv ℝ g y‖≤ε) →
      (∫ y in K, (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3)≤C*ε^2 := by
  let a := fun y : ℂ × ℝ => (y.2^3)⁻¹+(Module.finrank ℝ CubicThetaTangent:ℝ)/y.2
  have ha : ContinuousOn a K :=
    (((continuous_snd.pow 3).continuousOn).inv₀ (fun y hy => pow_ne_zero 3 (hpos hy).ne')).add
      (continuousOn_const.div continuous_snd.continuousOn (fun y hy => (hpos hy).ne'))
  have hai := ha.integrableOn_compact (μ:=volume) hK
  refine ⟨∫ y in K, a y,?_,fun g hg ε hε hv hd => ?_⟩
  · apply setIntegral_nonneg hK.measurableSet
    intro y hy
    exact add_nonneg (inv_nonneg.mpr (pow_nonneg (hpos hy).le 3))
      (div_nonneg (Nat.cast_nonneg _) (hpos hy).le)
  · have hcont : ContinuousOn
        (fun y => (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3) K :=
      (((hg.continuous.norm.pow 2).continuousOn.add
        ((continuous_snd.pow 2).mul (cubicThetaFunctionEnergy_continuous hg)).continuousOn)).div
          (continuous_snd.pow 3).continuousOn (fun y hy => pow_ne_zero 3 (hpos hy).ne')
    calc
      _ ≤ ∫ y in K, a y*ε^2 :=
        setIntegral_mono_on (hcont.integrableOn_compact hK) (hai.mul_const _) hK.measurableSet
          (fun y hy => cubicThetaCoordinateEnergy_density_bound hε hv hd (hpos hy))
      _ = _ := integral_mul_const _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateIntegrability
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability in the actual positive-height coordinates retains
the precise hyperbolic density v^-3. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointIntegrable_density {S : Set CubicThetaPoint} (hS : MeasurableSet S)
    (f : ℂ × ℝ → ℝ) :
    IntegrableOn (fun p => f (cubicThetaPointCoordinates p)) S cubicThetaPointMeasure ↔
      IntegrableOn (fun y => f y/y.2^3) (cubicThetaPointCoordinates '' S) := by
  have hT := cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS
  have hc := (cubicThetaPointInclusion_measurableEmbedding.integrable_map_iff
    (μ:=cubicThetaPointMeasure.restrict S) (g:=f)).symm
  rw [cubicThetaPointCoordinates_map_restrict hS] at hc
  change IntegrableOn (fun p => f (cubicThetaPointCoordinates p)) S cubicThetaPointMeasure ↔ _ at hc
  rw [hc]
  unfold IntegrableOn cubicThetaHyperbolicMeasure
  rw [restrict_withDensity hT,integrable_withDensity_iff_integrable_smul'
    cubicThetaHyperbolicDensity_measurable (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [ae_restrict_mem hT] with y hy
  obtain ⟨p,hp,rfl⟩ := hy
  have hv : 0<(cubicThetaPointCoordinates p).2 := p.property
  rw [cubicThetaHyperbolicDensity,ENNReal.toReal_ofReal
    (inv_nonneg.mpr (pow_nonneg hv.le 3))]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspVerticalEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial derivative in a cusp is controlled by the actual
hyperbolic Dirichlet energy of the pulled-back cubic section. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_apply (L : CubicThetaTangent →L[ℝ] ℂ) (u : CubicThetaTangent) :
    ‖L u‖^2 ≤ cubicThetaTangentEnergy L*‖u‖^2 := by
  have he : cubicThetaTangentEnergy L=
      ‖Complex.reCLM.comp L‖^2+‖Complex.imCLM.comp L‖^2 :=
    cubicThetaTangentEnergy_basis cubicThetaTangentBasis L
  have hr := (Complex.reCLM.comp L).le_opNorm u
  have hi := (Complex.imCLM.comp L).le_opNorm u
  have hr2 := (sq_le_sq₀ (_root_.norm_nonneg ((Complex.reCLM.comp L) u))
    (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg u))).mpr hr
  have hi2 := (sq_le_sq₀ (_root_.norm_nonneg ((Complex.imCLM.comp L) u))
    (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg u))).mpr hi
  rw [he,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp only [ContinuousLinearMap.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    Real.norm_eq_abs,sq_abs,mul_pow] at hr2 hi2
  nlinarith

def cubicThetaVerticalTangent : CubicThetaTangent := cubicThetaTangentCoordinates.symm (0,1)

lemma cubicThetaVerticalTangent_norm : ‖cubicThetaVerticalTangent‖=1 := by
  have h := cubicThetaTangent_norm_sq cubicThetaVerticalTangent
  simp only [cubicThetaVerticalTangent,ContinuousLinearEquiv.apply_symm_apply,
    cubicThetaRadius,Complex.normSq_zero,one_pow,zero_add] at h
  change ‖cubicThetaVerticalTangent‖^2=1 at h
  nlinarith [_root_.norm_nonneg cubicThetaVerticalTangent]

def cubicThetaVerticalPoint (z : ℂ) (v : ℝ) (hv : 0<v) : CubicThetaPoint := ⟨(z,v),hv⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFunctionEnergyTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transformation and vertical formulas for the hyperbolic
energy of scalar coordinate functions. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaFunctionEnergy_mobius (f : ℂ × ℝ → ℂ) (g : SL(2,ℂ))
    {p : ℂ × ℝ} (hp : 0<p.2) (hf : DifferentiableAt ℝ f (cubicThetaMobius g p)) :
    p.2^2*cubicThetaFunctionEnergy (fun q => f (cubicThetaMobius g q)) p=
      (cubicThetaMobius g p).2^2*cubicThetaFunctionEnergy f (cubicThetaMobius g p) := by
  have hM := (cubicThetaMobius_contDiffAt g hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hcomp := fderiv_comp p hf hM
  simp only [Function.comp_def] at hcomp
  have he : (fderiv ℝ (fun q => f (cubicThetaMobius g q)) p).comp
      cubicThetaTangentCoordinates.toContinuousLinearMap=
      ((fderiv ℝ f (cubicThetaMobius g p)).comp cubicThetaTangentCoordinates.toContinuousLinearMap).comp
        (cubicThetaTangentDerivative g p) := by
    rw [hcomp]
    ext u
    simp only [cubicThetaTangentDerivative,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
  unfold cubicThetaFunctionEnergy
  rw [he,cubicThetaTangentEnergy_derivative _ g hp]
  field_simp [hp.ne']

lemma cubicThetaFunctionEnergy_vertical {f : ℝ → ℂ} {p : ℂ × ℝ}
    (hf : DifferentiableAt ℝ f p.2) :
    cubicThetaFunctionEnergy (fun q => f q.2) p=‖deriv f p.2‖^2 := by
  have hs : DifferentiableAt ℝ (fun q : ℂ × ℝ => q.2) p := differentiableAt_snd
  have he := fderiv_comp p hf hs
  simp only [Function.comp_def] at he
  have hd := hf.hasDerivAt.hasFDerivAt.fderiv
  have hds := (hasFDerivAt_snd (𝕜:=ℝ) (E:=ℂ) (F:=ℝ) (p:=p)).fderiv
  unfold cubicThetaFunctionEnergy
  rw [cubicThetaTangentEnergy_coordinates,he,hd,hds]
  simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteEnergySum
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite sum estimate for the literal squared differential norm. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_sum_le {ι : Type*} (S : Finset ι)
    (L : ι → CubicThetaTangent →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (∑ i∈S,L i)≤
      (S.card:ℝ)*∑ i∈S,cubicThetaTangentEnergy (L i) := by
  classical
  unfold cubicThetaTangentEnergy
  calc
    _ ≤ ∑ j, (S.card:ℝ)*∑ i∈S,‖L i (cubicThetaTangentBasis j)‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      simp only [sum_apply]
      have hsq := mul_self_le_mul_self (_root_.norm_nonneg _) (norm_sum_le S
        (fun i => L i (cubicThetaTangentBasis j)))
      rw [← pow_two,← pow_two] at hsq
      exact hsq.trans (sq_sum_le_card_mul_sum_sq (s:=S)
        (f:=fun i => ‖L i (cubicThetaTangentBasis j)‖))
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]

lemma cubicThetaFunctionEnergy_sum_le {ι : Type*} (S : Finset ι)
    (f : ι → ℂ × ℝ → ℂ) (p : ℂ × ℝ)
    (hf : ∀ i∈S,DifferentiableAt ℝ (f i) p) :
    cubicThetaFunctionEnergy (fun y => ∑ i∈S,f i y) p≤
      (S.card:ℝ)*∑ i∈S,cubicThetaFunctionEnergy (f i) p := by
  have he : (fderiv ℝ (fun y => ∑ i∈S,f i y) p).comp cubicThetaTangentCoordinates.toContinuousLinearMap=
      ∑ i∈S,(fderiv ℝ (f i) p).comp cubicThetaTangentCoordinates.toContinuousLinearMap := by
    rw [fderiv_fun_sum hf]
    ext u
    simp only [ContinuousLinearMap.comp_apply,sum_apply]
  unfold cubicThetaFunctionEnergy
  rw [he]
  exact cubicThetaTangentEnergy_sum_le S _

lemma cubicThetaFunctionEnergy_one_sub {f : ℂ × ℝ → ℂ} {p : ℂ × ℝ}
    (hf : DifferentiableAt ℝ f p) :
    cubicThetaFunctionEnergy (fun y => 1-f y) p=cubicThetaFunctionEnergy f p := by
  have he : fderiv ℝ (fun y => 1-f y) p= -(fderiv ℝ f p) := by
    rw [fderiv_fun_sub (differentiableAt_const _) hf,fderiv_const_apply,zero_sub]
  simp only [cubicThetaFunctionEnergy,he,cubicThetaTangentEnergy,
    ContinuousLinearMap.comp_apply,neg_apply,norm_neg]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcingProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The forcing profile is an entire function with values in the
supremum-norm space on the fixed radial annulus. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaForcingLog : C(CubicThetaForcingBand,ℂ) :=
  ⟨fun v => (Real.log v.val:ℂ), Complex.continuous_ofReal.comp
    (continuous_subtype_val.log (fun v => ne_of_gt (lt_of_lt_of_le zero_lt_one v.property.1)))⟩

def cubicThetaForcingA : C(CubicThetaForcingBand,ℂ) :=
  ⟨fun v => (v.val:ℂ)^2*deriv (deriv cubicThetaCuspCutoff) v.val-
    (v.val:ℂ)*deriv cubicThetaCuspCutoff v.val,by
    have hd := (contDiff_infty_iff_deriv.mp cubicThetaCuspCutoff_smooth).2
    have hdd := (contDiff_infty_iff_deriv.mp hd).2
    have hc := Complex.continuous_ofReal.comp (continuous_subtype_val (p:=fun v : ℝ => v∈Set.Icc 1 2))
    exact ((hc.pow 2).mul (hdd.continuous.comp continuous_subtype_val)).sub
      (hc.mul (hd.continuous.comp continuous_subtype_val))⟩

def cubicThetaForcingB : C(CubicThetaForcingBand,ℂ) :=
  ⟨fun v => 2*(v.val:ℂ)*deriv cubicThetaCuspCutoff v.val,by
    have hd := (contDiff_infty_iff_deriv.mp cubicThetaCuspCutoff_smooth).2
    exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val)).mul
      (hd.continuous.comp continuous_subtype_val)⟩

def cubicThetaForcingProfile (s : ℂ) : C(CubicThetaForcingBand,ℂ) :=
  cubicThetaForcingA*NormedSpace.exp (s • cubicThetaForcingLog)+
    s • (cubicThetaForcingB*NormedSpace.exp (s • cubicThetaForcingLog))

theorem cubicThetaForcingProfile_analytic (s : ℂ) :
    AnalyticAt ℂ cubicThetaForcingProfile s := by
  have hl : AnalyticAt ℂ (fun z : ℂ => z • cubicThetaForcingLog) s :=
    analyticAt_id.smul analyticAt_const
  have he := (NormedSpace.exp_analytic (𝕂:=ℂ) (s • cubicThetaForcingLog)).comp
    (f:=fun z : ℂ => z • cubicThetaForcingLog) (x:=s) hl
  exact (analyticAt_const.mul he).add (analyticAt_id.smul (analyticAt_const.mul he))

lemma cubicThetaForcingProfile_apply (s : ℂ) (v : CubicThetaForcingBand) :
    cubicThetaForcingProfile s v=cubicThetaIncomingForcing s v.val := by
  have hv : 0<v.val := lt_of_lt_of_le zero_lt_one v.property.1
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (ContinuousMap.evalCLM (R:=ℂ) v).continuous (s • cubicThetaForcingLog)
  change (NormedSpace.exp (s • cubicThetaForcingLog)) v=
    NormedSpace.exp (s*(Real.log v.val:ℂ)) at he
  rw [← Complex.exp_eq_exp_ℂ] at he
  have hp : (NormedSpace.exp (s • cubicThetaForcingLog)) v=(v.val:ℂ)^s := by
    rw [he,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne'),
      ← Complex.ofReal_log hv.le,mul_comm]
  change cubicThetaForcingA v*(NormedSpace.exp (s • cubicThetaForcingLog)) v+
    s*(cubicThetaForcingB v*(NormedSpace.exp (s • cubicThetaForcingLog)) v)=_
  rw [hp]
  unfold cubicThetaForcingA cubicThetaForcingB cubicThetaIncomingForcing
  simp only [ContinuousMap.coe_mk]
  rw [Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hv.ne'),Complex.cpow_one]
  field_simp [Complex.ofReal_ne_zero.mpr hv.ne']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalLocalizationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundedness of each actual compact chart localization from the
global energy graph to its weighted local energy graph. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaLocalEnergyJet_zero {f : ℂ × ℝ → ℂ} {y : ℂ × ℝ}
    (hy : y∉tsupport f) : cubicThetaLocalEnergyJet f y=0 := by
  have hz := image_eq_zero_of_notMem_tsupport hy
  have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hy
  ext i
  fin_cases i <;> simp [cubicThetaLocalEnergyJet,hz,hd]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaL2Dominated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-integrable domination gives convergence of the actual L2
vectors. This is used for both values and tangent coordinates. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaL2_tendsto_of_dominated_sq
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {μ : Measure X} (f : ℕ → X → E) (g : X → E)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (b : X → ℝ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x-g x‖^2≤b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hi : Tendsto (fun n => ∫ x, ‖f n x-g x‖^2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ:=μ) (f:=fun _ => (0:ℝ)) b
      (fun n => ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2) hb
      (fun n => (hbound n).mono (fun x hx => by
        change |‖f n x-g x‖^2|≤b x
        rwa [abs_of_nonneg (sq_nonneg ‖f n x-g x‖)]))
      (hlim.mono (fun x hx => by simpa using (hx.sub_const (g x)).norm.pow 2))
    simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero] using h
  have he (n : ℕ) : ‖(hf n).toLp (f n)-hg.toLp g‖^2=∫ x, ‖f n x-g x‖^2 ∂μ := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp,hg.coeFn_toLp] with x hx hfx hgx
    simp only [Pi.sub_apply] at hx
    rw [hx,hfx,hgx]
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hi
    change Tendsto (fun n => Real.sqrt (∫ x, ‖f n x-g x‖^2 ∂μ)) atTop (𝓝 (Real.sqrt 0)) at h
    simp only [← he,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] at h
    exact h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSupportedTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported complex chart sections give actual supported
real Sobolev vectors. The Euclidean Rellich theorem applies to these
vectors, with the concrete transported compact support. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.tangent_borel
attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.tangent_borelSpace
lemma supported_test (g : C1c (E:=CubicThetaTangent))
    {S : Set CubicThetaTangent} (hS : MeasurableSet S) (hg : tsupport (g: CubicThetaTangent → ℝ)⊆S) :
    (⟨graph (μ:=tangentBorelVolume) g,Submodule.le_topologicalClosure _ ⟨g,rfl⟩⟩ :
      h1 (μ:=tangentBorelVolume))∈h1On S hS := by
  change toL2 (μ:=tangentBorelVolume) g∈LinearMap.range (Lp.extendByZeroₗᵢ hS).toLinearMap
  have hmem := memLp_of_mem_C1c (μ:=tangentBorelVolume) g.property
  let r := (hmem.restrict S).toLp (g:CubicThetaTangent → ℝ)
  refine ⟨r,?_⟩
  apply Lp.ext
  have hlocal : ∀ᵐ x ∂tangentBorelVolume, x∈S → r x=(g:CubicThetaTangent → ℝ) x :=
    (ae_restrict_iff' hS).mp (hmem.restrict S).coeFn_toLp
  filter_upwards [Lp.extendByZeroₗᵢ_ae_eq hS r,hmem.coeFn_toLp,hlocal] with x hxt hval hloc
  change (Lp.extendByZeroₗᵢ hS r) x=((hmem.toLp _) x)
  rw [hxt,hval]
  by_cases hx : x∈S
  · rw [Set.indicator_of_mem hx,hloc hx]
  · rw [Set.indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (hg ht))).symm

def realSupported {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hs : tsupport f⊆K) :
    h1On (cubicThetaTangentCoordinates ⁻¹' K)
      (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable) :=
  ⟨realH1 f hf hc,supported_test (realTest f hf hc) _ (realTest_support f hf hc hs)⟩

def imagSupported {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hs : tsupport f⊆K) :
    h1On (cubicThetaTangentCoordinates ⁻¹' K)
      (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable) :=
  ⟨imagH1 f hf hc,supported_test (imagTest f hf hc) _ (imagTest_support f hf hc hs)⟩

lemma supported_inclusion_compact {K : Set (ℂ × ℝ)} (hK : IsCompact K) :
    IsCompactOperator (h1OnToL2 (cubicThetaTangentCoordinates ⁻¹' K)
      (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable)) :=
  isCompactOperator_h1OnToL2
    (cubicThetaTangentCoordinates.toHomeomorph.isCompact_preimage.mpr hK) _

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalRellich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two supported real Sobolev components give a compact complex
L2 inclusion on every concrete compact coordinate set. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.localRellich_tangent_borel
attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.localRellich_tangent_borelSpace
abbrev Supported (K : Set (ℂ × ℝ)) (hK : IsCompact K) :=
  h1On (cubicThetaTangentCoordinates ⁻¹' K)
    (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable)

def realSupportedInclusion (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    Supported K hK →L[ℝ] Lp ℝ 2 tangentBorelVolume :=
  h1OnToL2 (cubicThetaTangentCoordinates ⁻¹' K)
    (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable)

def complexInclusion (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    (Supported K hK × Supported K hK) →L[ℝ] TangentComplexL2 :=
  ((Complex.ofRealCLM.compLpL 2 tangentBorelVolume).comp
    ((realSupportedInclusion K hK).comp (ContinuousLinearMap.fst ℝ _ _)))+
  Complex.I • ((Complex.ofRealCLM.compLpL 2 tangentBorelVolume).comp
    ((realSupportedInclusion K hK).comp (ContinuousLinearMap.snd ℝ _ _)))

theorem complexInclusion_compact (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    IsCompactOperator (complexInclusion K hK) := by
  have hc : IsCompactOperator (realSupportedInclusion K hK) := supported_inclusion_compact hK
  exact ((hc.comp_clm (ContinuousLinearMap.fst ℝ _ _)).clm_comp
      (Complex.ofRealCLM.compLpL 2 tangentBorelVolume)).add
    (((hc.comp_clm (ContinuousLinearMap.snd ℝ _ _)).clm_comp
      (Complex.ofRealCLM.compLpL 2 tangentBorelVolume)).smul Complex.I)

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalEnergyRellich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rellich compactness on the completion of the actual local energy
graph. No independent value and derivative data are introduced. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.energyRellich_borel
attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.energyRellich_borelSpace
lemma supported_closed (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    IsClosed (h1On (cubicThetaTangentCoordinates ⁻¹' K)
      (hK.isClosed.measurableSet.preimage cubicThetaTangentCoordinates.continuous.measurable) :
        Set (h1 (E:=CubicThetaTangent) (μ:=(volume : Measure CubicThetaTangent)))) := by
  exact (isClosed_range_extendByZero _ _).preimage
    (h1ToL2 (μ:=(volume : Measure CubicThetaTangent))).continuous

instance supported_complete (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    CompleteSpace (Supported K hK) := (supported_closed K hK).isComplete.completeSpace_coe

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalRellichValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact local energy inclusion has the original localized
complex section as its value, rather than an unrelated Sobolev vector. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.rellichValue_borel
attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.rellichValue_borelSpace
theorem complexInclusion_value {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hs : tsupport f⊆K) :
    complexInclusion K hK (realSupported hK f hf hc hs,imagSupported hK f hf hc hs)=
      tangentFunctionL2 f hf hc := by
  let r := toL2 (μ:=tangentBorelVolume) (realTest f hf hc)
  let i := toL2 (μ:=tangentBorelVolume) (imagTest f hf hc)
  have hr : (r:CubicThetaTangent → ℝ)=ᵐ[tangentBorelVolume]
      fun u => (f (cubicThetaTangentCoordinates u)).re :=
    (memLp_of_mem_C1c (μ:=tangentBorelVolume) (realTest f hf hc).property).coeFn_toLp
  have hi : (i:CubicThetaTangent → ℝ)=ᵐ[tangentBorelVolume]
      fun u => (f (cubicThetaTangentCoordinates u)).im :=
    (memLp_of_mem_C1c (μ:=tangentBorelVolume) (imagTest f hf hc).property).coeFn_toLp
  change Complex.ofRealCLM.compLp r+Complex.I • Complex.ofRealCLM.compLp i=tangentFunctionL2 f hf hc
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (Complex.ofRealCLM.compLp r) (Complex.I • Complex.ofRealCLM.compLp i),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLp i),
    Complex.ofRealCLM.coeFn_compLp r,Complex.ofRealCLM.coeFn_compLp i,hr,hi,
    (tangentFunction_memLp f hf hc).coeFn_toLp] with u ha hm hcr hci hru hiu hfu
  simp only [Pi.add_apply,Pi.smul_apply] at ha hm
  rw [ha,hm,hcr,hci,hru,hiu]
  change (f (cubicThetaTangentCoordinates u)).re+
    Complex.I*(f (cubicThetaTangentCoordinates u)).im=_
  change _=((tangentFunction_memLp f hf hc).toLp _) u
  rw [hfu]
  simpa only [mul_comm,Function.comp_apply] using Complex.re_add_im (f (cubicThetaTangentCoordinates u))

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous periodic horizontal slices of the actual automorphic
sections, with their genuine finite cell integrals. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalPoint (v : ℝ) (hv : 0<v) (z : ℂ) : CubicThetaPoint := ⟨(z,v),hv⟩

end CubicFirstMoment

end

end OAI
end


