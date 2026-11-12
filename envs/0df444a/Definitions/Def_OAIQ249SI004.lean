-- Prove2me | Definitions.Def_OAIQ249SI004
-- name    : OAIQ249SI004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:05:30.160193+00:00
-- url     : https://prove2.me/theorems/6d35e238-9d5c-4343-bd2e-68e750e2c469
-- title:
--   Definitions bundle OAIQ249SI004 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 385 declarations of OpenAI's Lean: 182 definitions, 12 inductive types or structures, 4 instances and 187 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapConnectingArc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.transverseVector`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.FrozenTranslationGerms`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.HasRelativeDefectFilling`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.LocalCornerBridge`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.LocalCornerBridge.leftPoint`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.LocalCornerBridge.mono`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.LocalCornerBridge.rightPoint`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.normalizedStepBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PrimitiveAmplitudeData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PrimitiveOperatorData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.QuadraticCrosscapGerms`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ShiftedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothDoubleArc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothDoubleChart`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothDoubleChart.overlap`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothDoubleChart.transition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.C1Bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleTransition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coordinateCore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coreThreshold`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.covectorFrame`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.error`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.pairSupport`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.pairWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitivePhaseCovector`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.projectionJet`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.singleTensorCentersDecidableEq`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorDecode`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorDecodeLM`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorOperatorFrame`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.weightCore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfaceCrosscapCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfaceCrosscapCoordinates.axisCurve` and 154 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_CoordinateBounds`, `Immersion_ClosedSurface_NormalFrame`, `Immersion_ClosedSurface_QuadraticError`, `Immersion_ClosedSurface_QuadraticMean`, `Immersion_ClosedSurface_WeightedBounds`, `SurfaceImmersion_Atlas_AtlasWeightedBounds`, `SurfaceImmersion_Atlas_CoordinatePushforward`, `SurfaceImmersion_Atlas_SupportedChartPullback`, `SurfaceImmersion_Atlas_SupportedCoordinateChange`, `SurfaceImmersion_Atlas_SupportedPhaseOperators`, `SurfaceImmersion_Atlas_TensorChartRead`, `SurfaceImmersion_Atlas_TensorPlaneCoordinates`, `SurfaceImmersion_Correction_ActualSmoothedStep`, `SurfaceImmersion_Correction_AtlasFreeOscillation`, `SurfaceImmersion_Correction_BundleSmoothingLinearity`, `SurfaceImmersion_Correction_BundleSmoothingTransition`, `SurfaceImmersion_Correction_C1ManifoldSmoothing`, `SurfaceImmersion_Correction_ConjugatedPolynomialOperator`, `SurfaceImmersion_Correction_FiniteOrderSmoother`, `SurfaceImmersion_Correction_FiniteSmootherApproximation`, `SurfaceImmersion_Correction_GlobalOscillatoryModes`, `SurfaceImmersion_Correction_GlobalShiftedSmoothing`, `SurfaceImmersion_Correction_JetPolynomialOperations`, `SurfaceImmersion_Correction_JetPolynomialScalar`, `SurfaceImmersion_Correction_ManifoldSmoothing`, `SurfaceImmersion_Correction_MixedJetPolynomial`, `SurfaceImmersion_Correction_ModulatedPolynomialJets`, `SurfaceImmersion_Correction_NormalizedPolynomialMean`, `SurfaceImmersion_Correction_NormalizedPolynomialSupport`, `SurfaceImmersion_Correction_PolynomialDiagonalVariations`, `SurfaceImmersion_Correction_PolynomialLinearModes`, `SurfaceImmersion_Correction_PolynomialMeanCoefficient`, `SurfaceImmersion_Correction_PolynomialMeanPair`, `SurfaceImmersion_Correction_PolynomialMeanSupport`, `SurfaceImmersion_Correction_PolynomialPerturbationBounds`, `SurfaceImmersion_Correction_PolynomialPhaseSupport`, `SurfaceImmersion_Correction_PolynomialQuadraticFamily`, `SurfaceImmersion_Correction_PolynomialQuadraticPhases`, `SurfaceImmersion_Correction_PolynomialQuadraticTargets`, `SurfaceImmersion_Correction_PolynomialTaylorRemainder`, `SurfaceImmersion_Correction_PolynomialVariationBounds`, `SurfaceImmersion_Correction_PolynomialVariationScaling`, `SurfaceImmersion_Correction_PolynomialZeroPhaseExpansion`, `SurfaceImmersion_Correction_ShiftedSmoothingBounds`, `SurfaceImmersion_Correction_SmoothPeriodicCalculus`, `SurfaceImmersion_Correction_SmoothedInputAdmissibility`, `SurfaceImmersion_Correction_SmoothingConvolution`, `SurfaceImmersion_Correction_SmoothingFirstMoment`, `SurfaceImmersion_Correction_SmoothingKernel`, `SurfaceImmersion_Correction_SmoothingMoments`, `SurfaceImmersion_Correction_SmoothingResidual`, `SurfaceImmersion_Correction_SmoothingTailBounds`, `SurfaceImmersion_Correction_SmoothingTransition`, `SurfaceImmersion_Correction_TensorAtlasMean`, `SurfaceImmersion_Correction_TensorMeanCoordinates`, `SurfaceImmersion_Correction_TensorMeanIteration`, `SurfaceImmersion_Correction_TensorSmoothing`, `SurfaceImmersion_Correction_WeightedPolynomialBounds`, `SurfaceImmersion_Geometry_C1ImmersionApproximation`, `SurfaceImmersion_Geometry_C1ImmersionJets`, `SurfaceImmersion_Geometry_CompactSectionBounds`, `SurfaceImmersion_Geometry_ComplexFirstVariation`, `SurfaceImmersion_Geometry_ComplexJetDecomposition`, `SurfaceImmersion_Geometry_ComplexMixedJets`, `SurfaceImmersion_Geometry_ComplexQuadraticVariation`, `SurfaceImmersion_Geometry_ComplexSlotAdditivity`, `SurfaceImmersion_Geometry_ConjugatedVariationBounds`, `SurfaceImmersion_Geometry_EuclideanRestoration`, `SurfaceImmersion_Geometry_FiniteQuadraticVariation`, `SurfaceImmersion_Geometry_FrozenTranslationGerms`, `SurfaceImmersion_Geometry_InputSize`, `SurfaceImmersion_Geometry_LocalizedBundleBounds`, `SurfaceImmersion_Geometry_LowJetChainRule`, `SurfaceImmersion_Geometry_MixedJetCalculus`, `SurfaceImmersion_Geometry_MixedJetHomogeneity`, `SurfaceImmersion_Geometry_MixedJetRegularity`, `SurfaceImmersion_Geometry_ModulatedJets`, `SurfaceImmersion_Geometry_PlaneComplexFrame`, `SurfaceImmersion_Geometry_RelativeDefectFilling`, `SurfaceImmersion_Geometry_SingleTensorRestoreBound`, `SurfaceImmersion_Geometry_SurfaceDirectionJet`, `SurfaceImmersion_Geometry_SurfaceInjectivityPatch`, `SurfaceImmersion_Geometry_SurfaceQuadraticTaylor`, `SurfaceImmersion_Geometry_TensorDecodedBounds`, `SurfaceImmersion_Geometry_TensorFrameAlgebra`, `SurfaceImmersion_Geometry_TensorOperatorFrame`, `SurfaceImmersion_Geometry_TensorPlaneReconstruction`, `SurfaceImmersion_Geometry_TensorRestoreFinite`, `SurfaceImmersion_Geometry_TransverseReflection`, `SurfaceImmersion_Primitive_AtlasPrimitiveOperator`, `SurfaceImmersion_Primitive_BoundaryProfileCoordinates`, `SurfaceImmersion_Primitive_BoundaryProfileGeometry`, `SurfaceImmersion_Primitive_LocalPeriodicCalculus`, `SurfaceImmersion_Primitive_LocalPeriodicFamilies`, `SurfaceImmersion_Primitive_PeriodicFamilies`, `SurfaceImmersion_Primitive_PrimitiveAmplitudeChain`, `SurfaceImmersion_Primitive_PrimitiveAmplitudeParameterBounds`, `SurfaceImmersion_Primitive_PrimitiveFiberInverse`, `SurfaceImmersion_Primitive_PrimitiveOperatorStability`, `SurfaceImmersion_Primitive_SlowPeriodicDerivative`, `SurfaceImmersion_Primitive_VelocityCircleLift`, `SurfaceImmersion_Primitive_VelocityCoordinateData`, `SurfaceImmersion_Primitive_VelocityFrame`, `SurfaceImmersion_Whitney_ArcTimeChartPartition`, `SurfaceImmersion_Whitney_CenteredCrosscapPreparation`, `SurfaceImmersion_Whitney_CompactDoublePairs`, `SurfaceImmersion_Whitney_CornerBridgePath`, `SurfaceImmersion_Whitney_CornerChartReflection`, `SurfaceImmersion_Whitney_CrosscapAxisCurve`, `SurfaceImmersion_Whitney_CrosscapConnectingArc`, `SurfaceImmersion_Whitney_CrosscapCoordinateStrip`, `SurfaceImmersion_Whitney_CrosscapStripFrame`, `SurfaceImmersion_Whitney_FiniteCrosscapCleanup`, `SurfaceImmersion_Whitney_FiniteSingularProjection`, `SurfaceImmersion_Whitney_FixedSurfacePairPatch`, `SurfaceImmersion_Whitney_LocalCornerBridge`, `SurfaceImmersion_Whitney_QuadraticCrosscapFactorization`, `SurfaceImmersion_Whitney_RegularPathCornerChart`, `SurfaceImmersion_Whitney_SeparatedCornerBridge`, `SurfaceImmersion_Whitney_ShiftedRotationFrame`, `SurfaceImmersion_Whitney_SmoothDoubleArc`, `SurfaceImmersion_Whitney_SmoothDoubleAtlas`, `SurfaceImmersion_Whitney_StandardPreparedCrosscaps`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundles `OAIQ249SI001` and `OAIQ249SI002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI006`, `OAIQ249SI007`, `OAIQ249SI008` and `OAIQ249SI009`; the statements `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_geometry_of_chartwise_good`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_background_metric_lower_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_convex_circular_atlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_induced_metric_upper_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfacePairTranslationPatch.regularize_avoiding_points`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cancel_crosscap_pair`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_source_embedded_path_regular`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_regular_crosscap_map`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finite_surface_pair_clean_relative`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_crosscap_ordered_arc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.remove_finite_quadratic_crosscaps`, `OAI_ClosedSurfaceR4_PhaseGeometry_positive_good_phase_data`, `OAI_ClosedSurfaceR4_PhaseGrid_compact_anchored_polynomial_grid`, `OAI_ClosedSurfaceR4_PhaseMean_polynomial_linear_mean_budgets` and `OAI_ClosedSurfaceR4_RealModes_inverse_normal_phase_bound`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfacePairTranslationPatch.regularize_avoiding_points`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_regular_crosscap_map`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finite_surface_pair_clean_relative`, `OAI_ClosedSurfaceR4_PhaseGeometry_inverse_normal_nonlinear_chart_bound`, `OAI_ClosedSurfaceR4_PhaseGeometry_polynomial_inverse_chart_bound`, `OAI_ClosedSurfaceR4_PhaseGeometry_positive_good_phase_data`, `OAI_ClosedSurfaceR4_PhaseGeometry_reciprocal_second_length_bound`, `OAI_ClosedSurfaceR4_PhaseGrid_compact_anchored_polynomial_grid`, `OAI_ClosedSurfaceR4_RealModes_inverse_normal_phase_bound`, `OAI_ClosedSurfaceR4_RealModes_polynomial_inverse_chart_twoJet_bound`, `OAI_ClosedSurfaceR4_RealModes_polynomial_nonlinear_phase_frame_bound`, `OAI_ClosedSurfaceR4_RealModes_realTwoJet_coordinate_prefix_bound` and `OAI_ClosedSurfaceR4_RealModes_realTwoJet_linear_prefix_bound`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI001
import Definitions.Def_OAIQ249SI002

section
-- module Solutions.OAIQ249_SI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.NormalFrame

def minor3 (X Y B : Vec) (i j k : Fin 4) : ℝ :=
  X i * (Y j * B k - Y k * B j) - X j * (Y i * B k - Y k * B i) +
    X k * (Y i * B j - Y j * B i)



def perpProduct (X Y B : Vec) : Vec :=
  ![-minor3 X Y B 1 2 3, minor3 X Y B 0 2 3,
    -minor3 X Y B 0 1 3, minor3 X Y B 0 1 2]

def unitPerp (X Y B : Vec) : Vec :=
  (Real.sqrt (perpProduct X Y B ⬝ᵥ perpProduct X Y B))⁻¹ • perpProduct X Y B

lemma dot_perp_left (X Y B : Vec) : X ⬝ᵥ perpProduct X Y B = 0 := by
  simp [dotProduct, Fin.sum_univ_succ, perpProduct, minor3]
  ring

lemma dot_perp_middle (X Y B : Vec) : Y ⬝ᵥ perpProduct X Y B = 0 := by
  simp [dotProduct, Fin.sum_univ_succ, perpProduct, minor3]
  ring

lemma dot_perp_right (X Y B : Vec) : B ⬝ᵥ perpProduct X Y B = 0 := by
  simp [dotProduct, Fin.sum_univ_succ, perpProduct, minor3]
  ring

lemma perp_sq (X Y B : Vec) :
    perpProduct X Y B ⬝ᵥ perpProduct X Y B =
      gramDet X Y * (B ⬝ᵥ B) - (X ⬝ᵥ X) * (Y ⬝ᵥ B) ^ 2 -
        (Y ⬝ᵥ Y) * (X ⬝ᵥ B) ^ 2 + 2 * (X ⬝ᵥ Y) * (X ⬝ᵥ B) * (Y ⬝ᵥ B) := by
  simp [dotProduct, Fin.sum_univ_succ, perpProduct, minor3, gramDet]
  ring

lemma gramDet_sum_sq (X Y : Vec) : gramDet X Y =
    (X 0 * Y 1 - X 1 * Y 0) ^ 2 + (X 0 * Y 2 - X 2 * Y 0) ^ 2 +
    (X 0 * Y 3 - X 3 * Y 0) ^ 2 + (X 1 * Y 2 - X 2 * Y 1) ^ 2 +
    (X 1 * Y 3 - X 3 * Y 1) ^ 2 + (X 2 * Y 3 - X 3 * Y 2) ^ 2 := by
  simp [gramDet, dotProduct, Fin.sum_univ_succ]
  ring

lemma gramDet_nonneg (X Y : Vec) : 0 ≤ gramDet X Y := by
  rw [gramDet_sum_sq]
  positivity

lemma gramDet_pos {X Y : Vec} (h : gramDet X Y ≠ 0) : 0 < gramDet X Y :=
  (gramDet_nonneg X Y).lt_of_ne' h

lemma perp_sq_pos {X Y B : Vec} (hD : gramDet X Y ≠ 0) (hB : B ≠ 0)
    (hX : X ⬝ᵥ B = 0) (hY : Y ⬝ᵥ B = 0) :
    0 < perpProduct X Y B ⬝ᵥ perpProduct X Y B := by
  rw [perp_sq, hX, hY]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero]
  have hb : 0 < B ⬝ᵥ B := by
    have hbb : 0 ≤ B ⬝ᵥ B := Finset.sum_nonneg (fun i _ => mul_self_nonneg (B i))
    exact hbb.lt_of_ne' ((dotProduct_self_eq_zero).not.mpr hB)
  exact mul_pos (gramDet_pos hD) hb

lemma unitPerp_orthogonal (X Y B : Vec) :
    X ⬝ᵥ unitPerp X Y B = 0 ∧ Y ⬝ᵥ unitPerp X Y B = 0 ∧ B ⬝ᵥ unitPerp X Y B = 0 := by
  simp only [unitPerp, dotProduct_smul, smul_eq_mul, dot_perp_left, dot_perp_middle,
    dot_perp_right, mul_zero, and_self]

section Smoothness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X Y B : E → Vec} {p : E}

lemma contDiffAt_minor3 (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hB : ContDiffAt ℝ ∞ B p) (i j k : Fin 4) :
    ContDiffAt ℝ ∞ (fun q => minor3 (X q) (Y q) (B q) i j k) p := by
  have hx := contDiffAt_pi.mp hX
  have hy := contDiffAt_pi.mp hY
  have hb := contDiffAt_pi.mp hB
  exact ((hx i).mul (((hy j).mul (hb k)).sub ((hy k).mul (hb j)))).sub
    ((hx j).mul (((hy i).mul (hb k)).sub ((hy k).mul (hb i)))) |>.add
    ((hx k).mul (((hy i).mul (hb j)).sub ((hy j).mul (hb i))))

lemma contDiffAt_perpProduct (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hB : ContDiffAt ℝ ∞ B p) : ContDiffAt ℝ ∞ (fun q => perpProduct (X q) (Y q) (B q)) p := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (contDiffAt_minor3 hX hY hB 1 2 3).neg
  · exact contDiffAt_minor3 hX hY hB 0 2 3
  · exact (contDiffAt_minor3 hX hY hB 0 1 3).neg
  · exact contDiffAt_minor3 hX hY hB 0 1 2

lemma contDiffAt_unitPerp (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hB : ContDiffAt ℝ ∞ B p) (hD : gramDet (X p) (Y p) ≠ 0) (hb : B p ≠ 0)
    (hXB : X p ⬝ᵥ B p = 0) (hYB : Y p ⬝ᵥ B p = 0) :
    ContDiffAt ℝ ∞ (fun q => unitPerp (X q) (Y q) (B q)) p := by
  have hv := contDiffAt_perpProduct hX hY hB
  have hs : ContDiffAt ℝ ∞ (fun q => perpProduct (X q) (Y q) (B q) ⬝ᵥ
      perpProduct (X q) (Y q) (B q)) p :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hp := perp_sq_pos hD hb hXB hYB
  exact ((hs.sqrt (ne_of_gt hp)).inv (ne_of_gt (Real.sqrt_pos.2 hp))).smul hv

end Smoothness
end ClosedSurfaceR4.NormalFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.mono_const {U : Set E} {s C D : ℝ} {m : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hCD : C ≤ D) : WeightedBound U s m D f :=
  fun j hj x hx => (h j hj x hx).trans hCD

lemma WeightedBound.norm_le {U : Set E} {s C : ℝ} {m : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) {x : E} (hx : x ∈ U) : ‖f x‖ ≤ C := by
  simpa only [pow_zero, one_mul, norm_iteratedFDerivWithin_zero] using h 0 (Nat.zero_le m) x hx

lemma WeightedBound.deriv_le {U : Set E} {s C : ℝ} {m : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ m) {x : E} (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C / s ^ j := by
  apply (le_div_iff₀ (pow_pos hs j)).2
  simpa only [mul_comm] using h j hj x hx

lemma WeightedBound.add {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (C + D) (fun x => f x + g x) := by
  intro j hj x hx
  rw [fun_iteratedFDerivWithin_add_apply ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    ((hg.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx) hU hx]
  calc
    _ ≤ s ^ j * (‖iteratedFDerivWithin ℝ j f U x‖ + ‖iteratedFDerivWithin ℝ j g U x‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ C + D := by rw [mul_add]; exact add_le_add (hbf j hj x hx) (hbg j hj x hx)

lemma WeightedBound.linear {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (L : F →L[ℝ] G) :
    WeightedBound U s m (‖L‖ * C) (L ∘ f) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖L‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact L.norm_iteratedFDerivWithin_comp_left (n := j) (N := ∞) (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖L‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ ‖L‖ * C := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg _)



lemma WeightedBound.bilinear {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f : E → F} {g : E → G} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g)
    (B : F →L[ℝ] G →L[ℝ] H) :
    WeightedBound U s m (‖B‖ * (2 ^ m * C * D)) (fun x => B (f x) (g x)) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact B.norm_iteratedFDerivWithin_le_of_bilinear (n := j) (N := ∞) hf hg hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖B‖ * (s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖)) := by ring
    _ ≤ ‖B‖ * (2 ^ j * C * D) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
      exact weighted_binomial_bound hs hC hD j _ _ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
        (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num


lemma WeightedBound.clm_apply {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} {g : E → F} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x (g x)) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

lemma WeightedBound.pi {ι : Type*} [Fintype ι] {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {f : ι → E → F} (hs : 0 < s) (hC : 0 ≤ C)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) (hb : ∀ i, WeightedBound U s m C (f i)) :
    WeightedBound U s m C (fun x i => f i x) := by
  intro j hj x hx
  rw [iteratedFDerivWithin_pi_smooth hU hf hx j, ContinuousMultilinearMap.opNorm_pi]
  rw [mul_comm]
  apply (le_div_iff₀ (pow_pos hs j)).1
  exact (pi_norm_le_iff_of_nonneg (div_nonneg hC (pow_nonneg hs.le _))).2
    (fun i => (hb i).deriv_le hs hj hx)

lemma WeightedBound.component {ι : Type*} [Fintype ι] {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {f : E → ι → F} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (i : ι) :
    WeightedBound U s m C (fun x => f x i) := by
  have hh := hb.linear hU hs hf (ContinuousLinearMap.proj i)
  apply hh.mono_const
  apply mul_le_of_le_one_left hC
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, ContinuousLinearMap.proj_apply] using norm_le_pi_norm x i

lemma weightedBound_zero (U : Set E) (s : ℝ) (m : ℕ) :
    WeightedBound U s m 0 (fun _ : E => (0 : F)) := by
  intro j hj x hx
  simp

lemma WeightedBound.finset_sum {ι : Type*} {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} {m : ℕ} (hs : 0 ≤ s) (a : Finset ι) (C : ι → ℝ) (f : ι → E → F)
    (hf : ∀ i ∈ a, ContDiffOn ℝ ∞ (f i) U)
    (hb : ∀ i ∈ a, WeightedBound U s m (C i) (f i)) :
    WeightedBound U s m (∑ i ∈ a, C i) (fun x => ∑ i ∈ a, f i x) := by
  classical
  induction a using Finset.induction_on with
  | empty => simpa using weightedBound_zero U s m
  | @insert i a hi ih =>
    have ha := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    have hh := (hb i (Finset.mem_insert_self i a)).add hU hs
      (hf i (Finset.mem_insert_self i a))
      (ContDiffOn.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))) ha
    simpa only [Finset.sum_insert hi] using hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CoordinateBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]




lemma WeightedBound.comp_coordinates {U : Set E} {V : Set F}
    (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V) {s C D : ℝ} {m : ℕ}
    {f : E → F} {g : F → G} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hcoord : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C)
    (hb : WeightedBound V s m D g) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ C ^ i := by
    refine (hcoord i hi1 (hij.trans hj) x hx).trans ?_
    simpa only [pow_one] using pow_le_pow_right₀ hC hi1
  have ho (i : ℕ) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i g V (f x)‖ ≤ D / s ^ j := by
    refine (hb.deriv_le hs (hij.trans hj) (hUV hx)).trans ?_
    exact div_le_div_of_nonneg_left hD (pow_pos hs _) (pow_le_pow_of_le_one hs.le hs1 hij)
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx ho hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * (D / s ^ j) * C ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by field_simp
    _ ≤ (m.factorial : ℝ) * D * C ^ m := by gcongr

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean

def conjugate {n : ℕ} (Z : CVec n) : CVec n := fun i => star (Z i)

def realMode {n : ℕ} (θ : ℝ) (Z : CVec n) : RVec n := realPart (phase θ • Z)



def derivativeAmplitude {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (Z : Base → CVec n)
    (v : Base) (p : Base) : CVec n :=
  fderiv ℝ Z p v + (I / (τ : ℂ) * (fderiv ℝ φ p v : ℂ)) • Z p


def displacement {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (Z : Base → CVec n) : Base → RVec n :=
  fun p => realMode (φ p / τ) (Z p)



def zeroPair {n : ℕ} (A B : CVec n) : ℝ := (A ⬝ᵥ conjugate B).re / 2

def sumDisplacement {n : ℕ} {ι : Type*} [Fintype ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → Base → CVec n) : Base → RVec n :=
  fun p => ∑ i, displacement τ (φ i) (Z i) p

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.WeightedEstimates

lemma contDiffOn_conjugate {n : ℕ} {U : Set Base} {Z : Base → CVec n}
    (hZ : ContDiffOn ℝ ∞ Z U) : ContDiffOn ℝ ∞ (fun p => conjugate (Z p)) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hZ i)

lemma contDiffOn_zeroPair {n : ℕ} {U : Set Base} {A B : Base → CVec n}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun p => zeroPair (A p) (B p)) U := by
  have hc := contDiffOn_conjugate hB
  have hd : ContDiffOn ℝ ∞ (fun p => A p ⬝ᵥ conjugate (B p)) U :=
    ContDiffOn.sum (fun i _ => (contDiffOn_pi.mp hA i).mul (contDiffOn_pi.mp hc i))
  simpa only [Function.comp_def, halfReCLM_apply, zeroPair] using
    halfReCLM.contDiff.comp_contDiffOn hd

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_WeightedPolynomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for the finite higher-jet monomials in paper 094-01.
The loss exponent adds under products and is unchanged when the output
order increases; only the multiplicative constant depends on that order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.smul_real {U : Set A} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {c : A → ℝ} {f : A → E}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ContDiffOn ℝ ∞ c U) (hf : ContDiffOn ℝ ∞ f U)
    (hbc : WeightedBound U s m C c) (hbf : WeightedBound U s m D f) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => c x • f x) := by
  have h := hbc.bilinear hU hs hC hD hc hf hbf (ContinuousLinearMap.lsmul ℝ ℝ)
  apply h.mono_const
  exact mul_le_of_le_one_left (by positivity) ContinuousLinearMap.opNorm_lsmul_le

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetChainRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chain rule for coefficients depending on position and the actual
second jet of a map from a surface chart into four-space. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

def lowBasis (i : LowIndex) : LowJet := Pi.single i 1

def lowDerivative (G : Base → Space) (v : Fin 2) (p : Base) : LowJet
  | Sum.inl i => coordinateVector v i
  | Sum.inr (w, a) => jet G (v :: lowWord w) a p

lemma lowJet_coordinate_derivative (G : Base → Space) (v : Fin 2) (i : LowIndex) (p : Base) :
    fderiv ℝ (fun q => lowJet G q i) p (coordinateVector v) = lowDerivative G v p i := by
  cases i with
  | inl i =>
    change fderiv ℝ (ContinuousLinearMap.proj i : Base →L[ℝ] ℝ) p (coordinateVector v) = _
    rw [(ContinuousLinearMap.proj i : Base →L[ℝ] ℝ).fderiv]
    rfl
  | inr i => rfl

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingMoments
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite moment cancellation for smoothing kernels on the coordinate plane.
Distinct positive dilations give a kernel of mass one whose required low
moments vanish. This is the algebraic step in finite-order smoothing. -/
noncomputable section
open scoped BigOperators Matrix

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

def monomial (α : Fin 2 → ℕ) (x : Base) : ℝ := ∏ i, x i ^ α i

lemma monomial_smul (α : Fin 2 → ℕ) (a : ℝ) (x : Base) :
    monomial α (a • x) = a ^ degree α * monomial α x := by
  simp only [monomial, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    degree, Finset.prod_pow_eq_pow_sum]

/-- The normalized dilation is appropriate to the two-dimensional chart. -/
def dilate (K : Base → ℝ) (a : ℝ) (x : Base) : ℝ := (a ^ 2)⁻¹ * K (a⁻¹ • x)

lemma moment_dilate (K : Base → ℝ) (α : Fin 2 → ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ x, monomial α x * dilate K a x) = a ^ degree α * ∫ x, monomial α x * K x := by
  have hdim : Module.finrank ℝ Base = 2 := by simp [Base]
  have hm (x : Base) : monomial α x = a ^ degree α * monomial α (a⁻¹ • x) := by
    rw [← monomial_smul, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have heq : (fun x => monomial α x * dilate K a x) =
      (fun x => (a ^ degree α / a ^ 2) *
        ((fun y => monomial α y * K y) (a⁻¹ • x))) := by
    funext x
    rw [hm x]
    unfold dilate
    ring
  rw [heq, integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun x => monomial α x * K x) ha.le]
  rw [hdim, smul_eq_mul]
  field_simp [ha.ne']

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingKernel
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compactly supported smoothing kernels with arbitrarily many
vanishing moments, constructed from finitely many positive dilations. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

lemma continuous_monomial (α : Fin 2 → ℕ) : Continuous (monomial α) := by
  unfold monomial
  fun_prop

lemma smooth_dilate {K : Base → ℝ} (hK : ContDiff ℝ ∞ K) (a : ℝ) :
    ContDiff ℝ ∞ (dilate K a) :=
  contDiff_const.mul (hK.comp (contDiff_id.const_smul a⁻¹))

lemma compact_dilate {K : Base → ℝ} (hK : HasCompactSupport K) {a : ℝ} (ha : a ≠ 0) :
    HasCompactSupport (dilate K a) := by
  let e : Base ≃ₜ Base := Homeomorph.smul (Units.mk0 a⁻¹ (inv_ne_zero ha))
  have h := (hK.comp_homeomorph e).mul_left (f := fun _ => (a ^ 2)⁻¹)
  exact h

lemma integrable_moment_dilate {K : Base → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    (α : Fin 2 → ℕ) {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun x => monomial α x * dilate K a x) := by
  have hd : Continuous (dilate K a) :=
    continuous_const.mul (hK.comp (continuous_id.const_smul a⁻¹))
  exact ((continuous_monomial α).mul hd).integrable_of_hasCompactSupport
    (compact_dilate hKc ha).mul_left

lemma moment_sum_dilates {r : ℕ} {K : Base → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K)
    (b c : Fin (r + 1) → ℝ) (hb : ∀ i, 0 < b i) (α : Fin 2 → ℕ) :
    (∫ x, monomial α x * (∑ i, c i * dilate K (b i) x)) =
      (∑ i, c i * b i ^ degree α) * ∫ x, monomial α x * K x := by
  have hi (i : Fin (r + 1)) : Integrable (fun x => c i * (monomial α x * dilate K (b i) x)) :=
    (integrable_moment_dilate hK hKc α (hb i).ne').const_mul (c i)
  have heq : (fun x => monomial α x * (∑ i, c i * dilate K (b i) x)) =
      (fun x => ∑ i, c i * (monomial α x * dilate K (b i) x)) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul, moment_dilate K α (hb _)]
  simp only [← mul_assoc, ← Finset.sum_mul]

def basicBump : ContDiffBump (0 : Base) := ⟨1, 2, by norm_num, by norm_num⟩

def basicKernel : Base → ℝ := basicBump.normed volume

lemma smooth_basicKernel : ContDiff ℝ ∞ basicKernel := basicBump.contDiff_normed

lemma compact_basicKernel : HasCompactSupport basicKernel := basicBump.hasCompactSupport_normed

lemma integral_basicKernel : (∫ x, basicKernel x) = 1 := basicBump.integral_normed

/-- A concrete kernel used for finite-order smoothing. Its mass is one and
all nonconstant coordinate moments through degree `r` vanish. -/
theorem exists_smoothing_kernel (r : ℕ) :
    ∃ K : Base → ℝ, ContDiff ℝ ∞ K ∧ HasCompactSupport K ∧
      (∫ x, K x) = 1 ∧ ∀ α : Fin 2 → ℕ, 1 ≤ degree α → degree α ≤ r →
        (∫ x, monomial α x * K x) = 0 := by
  let f : Base → ℝ := basicKernel
  have hfs : ContDiff ℝ ∞ f := smooth_basicKernel
  have hfc : HasCompactSupport f := compact_basicKernel
  have hfi : (∫ x, f x) = 1 := integral_basicKernel
  let b : Fin (r + 1) → ℝ := fun i => ((i.val + 1 : ℕ) : ℝ)
  have hb (i : Fin (r + 1)) : 0 < b i := by dsimp [b] <;> positivity
  obtain ⟨c, hc⟩ := exists_positive_dilation_weights r
  let K : Base → ℝ := fun x => ∑ i, c i * dilate f (b i) x
  have hs : ContDiff ℝ ∞ K := ContDiff.sum (fun i _ => (contDiff_const (c := c i)).mul (smooth_dilate hfs (b i)))
  have hk : HasCompactSupport K := by
    have hh := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun i x => c i * dilate f (b i) x)
      (fun i _ => (compact_dilate hfc (hb i).ne').mul_left)
    have heq : (∑ i, fun x => c i * dilate f (b i) x) = K := by
      funext x
      simp only [K, Finset.sum_apply]
    exact heq ▸ hh
  refine ⟨K, hs, hk, ?_, ?_⟩
  · let α : Fin 2 → ℕ := fun _ => 0
    have hm := moment_sum_dilates hfs.continuous hfc b c hb α
    have hm' : (∫ x, K x) = (∑ i, c i) * ∫ x, f x := by
      simpa only [α, degree, Finset.sum_const_zero, monomial, pow_zero,
        Finset.prod_const_one, one_mul, mul_one] using hm
    rw [hfi, mul_one] at hm'
    exact hm'.trans (by simpa using hc 0)
  · intro α hα hαr
    have hm := moment_sum_dilates hfs.continuous hfc b c hb α
    let j : Fin (r + 1) := ⟨degree α, by omega⟩
    have hj : j ≠ 0 := by intro he; have := congrArg Fin.val he; dsimp [j] at this; omega
    have hcancel := hc j
    simp only [ite_eq_right_iff.mpr (fun h => (hj h).elim)] at hcancel
    have heq : (∑ i, c i * b i ^ degree α) = 0 := hcancel
    exact hm.trans (by rw [heq, zero_mul])

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothing operators from the finite-moment kernels. They are
linear on locally integrable inputs, smooth their outputs, and fix constants. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

def kernel (r : ℕ) : Base → ℝ := Classical.choose (exists_smoothing_kernel r)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Smoothing at scale `s`, using the kernel whose moments vanish through `r`. -/
def smooth (r : ℕ) (s : ℝ) (f : Base → E) : Base → E :=
  (dilate (kernel r) s) ⋆[lsmul ℝ ℝ, volume] f

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingFirstMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-moment control of the error of the actual convolution operator. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

def firstMoment (K : Base → ℝ) : ℝ := ∫ x, ‖K x‖ * ‖x‖

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterated smoothing residuals give arbitrary finite approximation order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def residual (s : ℝ) : ℕ → (Base → E) → (Base → E)
  | 0, f => f
  | n + 1, f => residual s n f - smooth 0 s (residual s n f)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteOrderSmoother
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete smoother of any prescribed finite approximation order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The finite sum `S + S(I-S) + ... + S(I-S)^(n-1)`. -/
def finiteSmooth (n : ℕ) (s : ℝ) (f : Base → E) : Base → E :=
  ∑ i ∈ Finset.range n, smooth 0 s (residual s i f)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSmootherApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-order smoother approximates using only the displayed finite
number of input derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def approximationConstant (r j : ℕ) : ℝ :=
  (1 + ∫ y, ‖kernel 0 y‖) ^ j * firstMoment (kernel 0) ^ (r - j)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

/-- The actual global operator; no choice in its definition depends on `f`. -/
def smooth (r : ℕ) (s : ℝ) (f : M → V) : M → V :=
  ∑ i : A.centers, restore (i : M) (A.outer i) (finiteSmooth r s (localize (i : M) (A.weight i) f))

/-- The corresponding global error, written entirely in coordinate residuals. -/
def error (r : ℕ) (s : ℝ) (f : M → V) : M → V :=
  ∑ i : A.centers, restore (i : M) (A.outer i) (residual s r (localize (i : M) (A.weight i) f))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def transition (p q : M) : OpenPartialHomeomorph Base Base := (chart p).symm.trans (chart q)

lemma transition_smooth (p q : M) :
    ContDiffOn ℝ ∞ (transition p q) (transition p q).source := by
  apply ContMDiffOn.contDiffOn
  exact (chart_smooth q).comp
    ((chart_symm_smooth p).mono (fun _ hx => hx.1)) (fun _ hx => hx.2)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def pairWeight (i j : A.centers) : Base → ℝ := localize (i : M) (A.weight i) (A.outer j)

def pairSupport (i j : A.centers) : Set Base :=
  (chart (i : M)) '' (tsupport (A.weight i) ∩ tsupport (A.outer j))

variable [CompactSpace M]

lemma pairWeight_support (i j : A.centers) : tsupport (A.pairWeight i j) ⊆ A.pairSupport i j :=
  localize_tsupport_inter (i : M) (A.weight_support i) (A.outer j)

lemma pairSupport_compact (i j : A.centers) : IsCompact (A.pairSupport i j) :=
  ((isClosed_tsupport (A.weight i)).inter (isClosed_tsupport (A.outer j))).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (fun _ hx => A.weight_support i hx.1))

omit [CompactSpace M] in
lemma pairSupport_transition (i j : A.centers) :
    A.pairSupport i j ⊆ (transition (i : M) (j : M)).source := by
  rintro x ⟨p, ⟨hp, hq⟩, rfl⟩
  have hp' := A.weight_support i hp
  refine ⟨(chart (i : M)).map_source hp', ?_⟩
  change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
  rw [(chart (i : M)).left_inv hp']
  exact A.outer_support j hq

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- A fixed finite family of localized coordinate norms. -/
def WeightedBound (t : ℝ) (m : ℕ) (C : ℝ) (f : M → V) : Prop :=
  ∀ i : A.centers, WeightedEstimates.WeightedBound Set.univ t m C
    (localize (i : M) (A.weight i) f)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_C1ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing C1 maps on the fixed finite surface atlas. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- The value and derivative bounds used to preserve immersion under smoothing. -/
def C1Bound (C : ℝ) (f : M → V) : Prop :=
  ∀ i : A.centers, ∀ x : Base,
    ‖localize (i : M) (A.weight i) f x‖ ≤ C ∧
    ‖fderiv ℝ (localize (i : M) (A.weight i) f) x‖ ≤ C

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionJets
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted first jets detect immersion on the region where a partition
weight is nonzero. They depend continuously on the localized C1 data. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def weightedJet (w : Base → ℝ) (l : Base → V) (x : Base) : Base →L[ℝ] V :=
  w x • fderiv ℝ l x - (fderiv ℝ w x).smulRight (l x)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

def localizedWeight (p : M) (ψ : M → ℝ) : Base → ℝ := localize p ψ (fun _ => 1)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinatePushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension of a supported coordinate change through any smooth surface
coordinate neighborhood, including the constructed crosscap coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M]
variable {V : Type*} [NormedAddCommGroup V]

def coordinatePushforward (c : OpenPartialHomeomorph M Base) (δ : Base → V) : M → V :=
  c.source.indicator (δ ∘ c)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedChartPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported pullback through a local chart, extended by a fixed
cutoff without altering the pullback on the chart's source. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def supportedChartPullback (e : OpenPartialHomeomorph Base Base) (χ : Base → ℝ)
    (f : Base → V) (x : Base) : V := χ x • f (e x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedCoordinateChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric linear coordinate changes preserve the supported weighted
seminorms exactly. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma weightedBound_comp_isometry (e : A ≃ₗᵢ[ℝ] B) {f : B → F}
    (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hb : WeightedBound Set.univ s m C f) :
    WeightedBound Set.univ s m C (f ∘ e) := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  change s ^ j * ‖iteratedFDeriv ℝ j
    (f ∘ (e.toContinuousLinearEquiv.toContinuousLinearMap : A → B)) x‖ ≤ C
  rw [e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
    ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
  change s ^ j * ‖iteratedFDeriv ℝ j f (e x)‖ ≤ C
  simpa only [iteratedFDerivWithin_univ] using hb j hj (e x) (Set.mem_univ _)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJets
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of the fast phase from arbitrary ordered directional jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates

def amplitudeDerivative (τ : ℝ) (φ : Base → ℝ) (v : Base) (Z : Base → ℂ) : Base → ℂ :=
  fun p => fderiv ℝ Z p v + (Complex.I / (τ : ℂ) * (fderiv ℝ φ p v : ℂ)) * Z p

def amplitudeJet (τ : ℝ) (φ : Base → ℝ) : List Base → (Base → ℂ) → Base → ℂ
  | [], Z => Z
  | v :: w, Z => amplitudeDerivative τ φ v (amplitudeJet τ φ w Z)

lemma amplitudeDerivative_smooth {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ : ℝ) (v : Base) :
    ContDiff ℝ ∞ (amplitudeDerivative τ φ v Z) := by
  have hdZ := (hZ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := v))
  have hdφ := (hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := v))
  exact hdZ.add ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hdφ)).mul hZ)

lemma amplitudeJet_smooth {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ : ℝ) (w : List Base) :
    ContDiff ℝ ∞ (amplitudeJet τ φ w Z) := by
  induction w with
  | nil => exact hZ
  | cons v w ih => exact amplitudeDerivative_smooth hφ ih τ v

lemma derivative_phase_product {φ : Base → ℝ} {Z : Base → ℂ} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (v : Base) :
    fderiv ℝ (fun q => phase τ φ q * Z q) p v =
      phase τ φ p * amplitudeDerivative τ φ v Z p := by
  have hp := ((Complex.ofRealCLM.hasFDerivAt.comp p hφ.hasFDerivAt).const_mul
    (Complex.I / (τ : ℂ))).cexp
  have h := hp.mul hZ.hasFDerivAt
  have hfun : ((fun x => Complex.exp (Complex.I / (τ : ℂ) *
      (Complex.ofRealCLM ∘ φ) x)) * Z) = (fun q => phase τ φ q * Z q) := rfl
  rw [← hfun, h.fderiv]
  simp only [amplitudeDerivative, phase, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Function.comp_def]
  ring

/-- Differentiating the oscillation changes its amplitude but preserves the
single phase factor, in every ordered coordinate word. -/
theorem iterated_phase_product {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ : ℝ) (w : List Base) :
    iteratedDirectional w (fun p => phase τ φ p * Z p) =
      fun p => phase τ φ p * amplitudeJet τ φ w Z p := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    rw [iteratedDirectional, ih]
    funext p
    exact derivative_phase_product (hφ.differentiable (by simp) p)
      ((amplitudeJet_smooth hφ hZ τ w).differentiable (by simp) p) τ v

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedPhaseOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Phase multiplication is an actual linear operator on supported smooth
fields, with the same fixed support. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℂ ℝ F]

namespace ModulatedJets

lemma phase_neg_inv (τ : ℝ) (φ : Base → ℝ) (p : Base) :
    phase τ (fun q => -φ q) p = (phase τ φ p)⁻¹ := by
  simp only [phase, Complex.ofReal_neg, mul_neg, Complex.exp_neg]

end ModulatedJets
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedBundleBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted bounds for localized vector-bundle transition operators. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma restricted_weighted_bound {U O : Set Base} (hU : IsOpen U)
    (hO : IsOpen O) (hUO : closure U ⊆ O) {f : Base → V}
    (hf : ContDiffOn ℝ ∞ f O) {m : ℕ} {A : ℝ}
    (hb : ∀ j ≤ m, ∀ x ∈ closure U, ‖iteratedFDerivWithin ℝ j f O x‖ ≤ A)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : WeightedBound U s m A f := by
  intro j hj x hx
  have ht : ContDiffAt ℝ (j : ℕ∞ω) f x :=
    (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hUO (subset_closure hx)))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
  have h := hb j hj x (subset_closure hx)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht
    (hUO (subset_closure hx))] at h
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h

/-- Smooth changes of fiber coordinates and base coordinates together cost
only a fixed constant in each weighted norm. -/
theorem compact_localized_clm_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {L : Base → V →L[ℝ] W} (hL : ContDiffOn ℝ ∞ L O)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • L x (f (T x))) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hL m
  obtain ⟨E, hE, hbE⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * (2 ^ m * B * ((m.factorial : ℝ) * E ^ m)), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ E := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbE j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb := restricted_weighted_bound hU hO hUO hχ.contDiffOn hbA hs hs1
  have hLb := restricted_weighted_bound hU hO hUO hL hbB hs hs1
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hE hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hlc := hLb.clm_apply hU.uniqueDiffOn hs.le (zero_le_one.trans hB)
    (by positivity) (hL.mono hsub) hcomp hc
  have hlcs : ContDiffOn ℝ ∞ (fun x => L x (f (T x))) U :=
    (hL.mono hsub).clm_apply hcomp
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hlcs hlc
  have hlocal := hχ.contDiffOn.smul hlcs
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • L x (f (T x))) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxχ : x ∉ tsupport χ := fun h => hx (hKU (hχK h))
    have heq : (fun y => χ y • L y (f (T y))) =ᶠ[𝓝 x] (fun _ => (0 : W)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chart transitions for the actual bundle smoother. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

def bundleTransition (i j : A.centers) (x : Base) : F →L[ℝ] F :=
  (e j).coordChangeL ℝ (e i) ((chart (i : M)).symm x)

variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

lemma bundleTransition_smooth (i j : A.centers) :
    ContDiffOn ℝ ∞ (A.bundleTransition e i j) (transition (i : M) (j : M)).source := by
  apply ContMDiffOn.contDiffOn
  apply (contMDiffOn_coordChangeL (e j) (e i)).comp
    ((chart_symm_smooth (i : M)).mono (fun _ hx => hx.1))
  intro x hx
  exact ⟨hdomain j hx.2, hdomain i ((chart (i : M)).map_target hx.1)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-input smoothing-tail estimate at every output order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory WeightedEstimates
open JetPolynomial (Base)

def tailConstant (r : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (r + 1), approximationConstant r j) +
    (1 + ∫ y, ‖kernel 0 y‖) ^ r

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing on the actual covariant two-tensor bundle of the surface. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle MeasureTheory
open JetPolynomial (Base)

local instance tensorModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorModelSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the concrete finite-atlas bundle smoother. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

lemma bundleRestore_add (i : A.centers) (f g : Base → F) :
    A.bundleRestore e i (f + g) = A.bundleRestore e i f + A.bundleRestore e i g := by
  funext x
  simp only [bundleRestore, Pi.add_apply, map_add, smul_add]

lemma bundleRestore_smul (i : A.centers) (a : ℝ) (f : Base → F) :
    A.bundleRestore e i (a • f) = a • A.bundleRestore e i f := by
  funext x
  simp only [bundleRestore, Pi.smul_apply, map_smul, smul_smul]
  rw [mul_comm]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encode global tensor sections by their finite atlas coordinates. This
retains the compact-surface partition identity while permitting the finite
mean iteration to run on a normed vector-valued function space. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

local instance meanModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance meanModelSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualSmul
local instance sectionTensorNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualSmul
variable (A : SmoothingAtlas M)

local instance sectionTensorSpace_r34e91d_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorDecode (f : Base → A.centers → TensorFiber) : ∀ x : M, CovariantTwoTensor x :=
  fun x => ∑ i : A.centers, A.bundleRestore A.tensorTriv i (fun y => f y i) x

lemma tensorDecode_add (f g : Base → A.centers → TensorFiber) :
    A.tensorDecode (f + g) = A.tensorDecode f + A.tensorDecode g := by
  funext x
  simp only [tensorDecode, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (A.bundleRestore_add A.tensorTriv i (fun y => f y i) (fun y => g y i)) x

lemma tensorDecode_smul (a : ℝ) (f : Base → A.centers → TensorFiber) :
    A.tensorDecode (a • f) = a • A.tensorDecode f := by
  funext x
  simp only [tensorDecode, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (A.bundleRestore_smul A.tensorTriv i a (fun y => f y i)) x

lemma tensorDecode_sub (f g : Base → A.centers → TensorFiber) :
    A.tensorDecode (f - g) = A.tensorDecode f - A.tensorDecode g := by
  funext x
  simp only [tensorDecode, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bundleRestore, map_sub, smul_sub]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth chart readings of tensors agree with unweighted components on
the phase support and are bounded by the fixed atlas seminorms. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates PhaseMean
open JetPolynomial (Base)

local instance chartReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance chartReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance chartReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance chartReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance planeReadFiberNormed_r34e91d_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance planeReadFiberSpace_r34e91d_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance planeReadDualAdd_r34e91d_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance planeReadDualSmul_r34e91d_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance planeReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def ShiftedBound (q m : ℕ) (s C : ℝ) (f : Base → V) : Prop :=
  ∀ j ≤ q + m, ∀ x, s ^ (j - q) * ‖iteratedFDeriv ℝ j f x‖ ≤ C

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalShiftedSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas smoothing with an unweighted derivative prefix. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold MeasureTheory
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Localized norms whose first `q` derivatives are unweighted. -/
def ShiftedBound (q m : ℕ) (s C : ℝ) (f : M → V) : Prop :=
  ∀ i : A.centers, FiniteOrderSmoothing.ShiftedBound q m s C
    (localize (i : M) (A.weight i) f)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPeriodicCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical periodic primitives and angular derivatives in a smooth family. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.SmoothPeriodicCalculus

open CovarianceCorrector PeriodicPrimitive PeriodicCalculus

variable {A E : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiff_angleDerivative {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (angleDerivative F) :=
  (hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

lemma angle_hasDerivAt {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (p : A) (t : ℝ) :
    HasDerivAt (fun s => F (p, s)) (angleDerivative F (p, t)) t := by
  have hi : HasFDerivAt (fun s : ℝ => (p, s)) (ContinuousLinearMap.inr ℝ A ℝ) t := by
    simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
      ((ContinuousLinearMap.inr ℝ A ℝ).hasFDerivAt (x := t)).add_const (p, 0)
  have hd := ((hF.differentiable (by simp) (p, t)).hasFDerivAt.comp t hi).hasDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    angleDerivative] using hd

lemma periodic_angleDerivative {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (hp : ∀ p, Function.Periodic (fun t => F (p, t)) 1) (p : A) :
    Function.Periodic (fun t => angleDerivative F (p, t)) 1 := by
  have he : (fun t => angleDerivative F (p, t)) = deriv (fun t => F (p, t)) :=
    funext (fun t => (angle_hasDerivAt hF p t).deriv.symm)
  rw [he]
  exact periodic_deriv (hp p)

def derivativeFamily (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))) : A → C(Period, E) :=
  bundleFamily (angleDerivative (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (contDiff_angleDerivative hF) (periodic_angleDerivative hF (periodic_lift F))

lemma derivativeFamily_smooth (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))) :
    ContDiff ℝ ∞ (fun z : A × ℝ => derivativeFamily F hF z.1 (z.2 : Period)) :=
  contDiff_angleDerivative hF

end ClosedSurfaceR4.SmoothPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SlowPeriodicDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Slow differentiation commutes with the periodic mean. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_slice {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (p v : A) (t : ℝ) :
    fderiv ℝ (fun q => F (q, t)) p v = slowDerivative F v (p, t) := by
  rw [(SmoothParameterIntegral.partial_hasFDerivAt hF p t).fderiv]
  rfl

lemma periodic_slowDerivative {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (hp : ∀ p, Function.Periodic (fun t => F (p, t)) 1) (v p : A) :
    Function.Periodic (fun t => slowDerivative F v (p, t)) 1 := by
  intro t
  have he : (fun q => F (q, t + 1)) = fun q => F (q, t) := funext (fun q => hp q t)
  have hd := congrArg (fun f : A → E => fderiv ℝ f p v) he
  simpa only [fderiv_slice hF] using hd

def slowDerivativeFamily (F : A → C(CovarianceCorrector.Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : CovarianceCorrector.Period))) (v : A) :
    A → C(CovarianceCorrector.Period, E) :=
  bundleFamily (slowDerivative (fun z : A × ℝ => F z.1 (z.2 : CovarianceCorrector.Period)) v)
    (contDiff_slowDerivative hF v) (periodic_slowDerivative hF (periodic_lift F) v)

lemma slowDerivativeFamily_smooth (F : A → C(CovarianceCorrector.Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : CovarianceCorrector.Period))) (v : A) :
    ContDiff ℝ ∞ (fun z : A × ℝ => slowDerivativeFamily F hF v z.1
      (z.2 : CovarianceCorrector.Period)) := contDiff_slowDerivative hF v

end ClosedSurfaceR4.SmoothPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def bundleOn (F : P × ℝ → E) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ))
    (hper : ∀ p ∈ S, Function.Periodic (fun t => F (p, t)) 1) : P → C(Period, E) := by
  classical
  exact fun p => if hp : p ∈ S then
    bundle (fun t => F (p, t)) (hper p hp) (smooth_slice hS hF hp).continuous else 0

lemma angle_smooth {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (angleDerivative F) (S ×ˢ Set.univ) :=
  (hF.fderiv_of_isOpen (hS.prod isOpen_univ) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const

lemma angle_hasDerivAt {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s => F (p, s)) (angleDerivative F (p, t)) t := by
  have hi : HasFDerivAt (fun s : ℝ => (p, s)) (ContinuousLinearMap.inr ℝ P ℝ) t := by
    simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
      ((ContinuousLinearMap.inr ℝ P ℝ).hasFDerivAt (x := t)).add_const (p, 0)
  have hd := ((hF.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp t hi
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    angleDerivative] using hd.hasDerivAt

lemma periodic_angle {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ))
    (hper : ∀ p ∈ S, Function.Periodic (fun t => F (p, t)) 1) {p : P} (hp : p ∈ S) :
    Function.Periodic (fun t => angleDerivative F (p, t)) 1 := by
  have he : (fun t => angleDerivative F (p, t)) = deriv (fun t => F (p, t)) :=
    funext (fun t => (angle_hasDerivAt hS hF hp t).deriv.symm)
  rw [he]
  exact PeriodicCalculus.periodic_deriv (hper p hp)

lemma periodic_slow (F : P → C(Period, E)) {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) {p : P} (hp : p ∈ S) :
    Function.Periodic (fun t => slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v (p, t)) 1 := by
  intro t
  have he : (fun q => F q ((t + 1 : ℝ) : Period)) = fun q => F q (t : Period) :=
    funext (fun q => periodic_lift F q t)
  have hd := congrArg (fun f : P → E => fderiv ℝ f p v) he
  simpa only [fderiv_slice hS hF hp] using hd

def angleOn (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    P → C(Period, E) :=
  bundleOn (angleDerivative (fun z : P × ℝ => F z.1 (z.2 : Period))) S hS
    (angle_smooth hS hF) (fun _ hp => periodic_angle hS hF (fun p _ => periodic_lift F p) hp)

def slowOn (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) : P → C(Period, E) :=
  bundleOn (slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v) S hS
    (slow_smooth hS hF v) (fun _ hp => periodic_slow F hS hF v hp)

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MixedJetPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomials in the base-map jet and three independent variation jets.
Differentiating the base map increases the scale loss by at most two. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

inductive MixedExpression where
  | coeff (c : LowJet × ℝ → ℝ)
  | atom (tag : Fin 4) (word : List (Fin 2)) (component : Fin 4) (tail : MixedExpression)
  | add (left right : MixedExpression)

namespace MixedExpression

def eval : MixedExpression → (Fin 4 → Base → Space) → Base × ℝ → ℝ
  | .coeff c, G, z => c (lowJet (G 0) z.1, z.2)
  | .atom i w a e, G, z => jet (G i) w a z.1 * e.eval G z
  | .add e f, G, z => e.eval G z + f.eval G z

def loss : MixedExpression → ℕ
  | .coeff _ => 0
  | .atom i w _ e => (if i = 0 then w.length - 2 else w.length) + e.loss
  | .add e f => max e.loss f.loss

def SmoothCoeffs (O : Set LowJet) : MixedExpression → Prop
  | .coeff c => ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)
  | .atom _ _ _ e => e.SmoothCoeffs O
  | .add e f => e.SmoothCoeffs O ∧ f.SmoothCoeffs O

def ofExpression : Expression → MixedExpression
  | .coeff c => .coeff c
  | .atom w a e => .atom 0 w a (ofExpression e)
  | .add e f => .add (ofExpression e) (ofExpression f)

def sumList {ι : Type*} : List ι → (ι → MixedExpression) → MixedExpression
  | [], _ => .coeff (fun _ => 0)
  | i :: l, f => .add (f i) (sumList l f)

def coefficientDerivative (c : LowJet × ℝ → ℝ) (i : Fin 7 × Fin 4) : LowJet × ℝ → ℝ :=
  fun z => fderiv ℝ c z (lowBasis (.inr i), 0)

/-- Only the base-map slot is differentiated. The new direction is one of
the three variation slots, so a third variation uses no extra map slots. -/
def differentiate (j : Fin 3) : MixedExpression → MixedExpression
  | .coeff c => sumList Finset.univ.toList (fun i : Fin 7 × Fin 4 =>
      .atom j.succ (lowWord i.1) i.2 (.coeff (coefficientDerivative c i)))
  | .atom i w a e => if i = 0 then
      .add (.atom j.succ w a e) (.atom i w a (differentiate j e))
    else .atom i w a (differentiate j e)
  | .add e f => .add (differentiate j e) (differentiate j f)

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial order and smoothness of mixed jet expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma smoothCoeffs_ofExpression {O : Set LowJet} {e : Expression} (he : e.SmoothCoeffs O) :
    (ofExpression e).SmoothCoeffs O := by
  induction e with
  | coeff => exact he
  | atom _ _ _ ih => exact ih he
  | add _ _ ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetCalculus
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coefficient part of the mixed polynomial variation is the actual
low-jet chain rule, with the position coordinates held fixed. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

namespace MixedExpression

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → MixedExpression)
    (h : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨h i (List.mem_cons_self ..),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩

theorem differentiate_smoothCoeffs {O : Set LowJet} (hO : IsOpen O) (j : Fin 3)
    {e : MixedExpression} (he : e.SmoothCoeffs O) : (e.differentiate j).SmoothCoeffs O := by
  induction e with
  | coeff c =>
    apply smoothCoeffs_sumList
    intro i _
    exact (he.fderiv_of_isOpen (hO.prod isOpen_univ) (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const
  | atom i w a e ih =>
    by_cases hi : i = 0
    · simpa only [differentiate, hi, ↓reduceIte, SmoothCoeffs] using And.intro he (ih he)
    · simpa only [differentiate, hi, ↓reduceIte, SmoothCoeffs] using ih he
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetHomogeneity
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homogeneity in each variation slot, including the zero polynomial. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

inductive DegreeIn (j : Fin 3) : MixedExpression → ℕ → Prop
  | coeff (c) : DegreeIn j (.coeff c) 0
  | zero (n) : DegreeIn j (.coeff (fun _ => 0)) n
  | other {e n} (i w a) (hi : i ≠ j.succ) (h : DegreeIn j e n) :
      DegreeIn j (.atom i w a e) n
  | same {e n} (w a) (h : DegreeIn j e n) : DegreeIn j (.atom j.succ w a e) (n + 1)
  | add {e f n} (he : DegreeIn j e n) (hf : DegreeIn j f n) : DegreeIn j (.add e f) n

lemma degree_sumList {ι : Type*} (j : Fin 3) (n : ℕ) (l : List ι) (f : ι → MixedExpression)
    (h : ∀ i ∈ l, DegreeIn j (f i) n) : DegreeIn j (sumList l f) n := by
  induction l with
  | nil => exact DegreeIn.zero n
  | cons i l ih =>
    exact DegreeIn.add (h i (List.mem_cons_self ..))
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

lemma degree_ofExpression (j : Fin 3) (e : Expression) : DegreeIn j (ofExpression e) 0 := by
  induction e with
  | coeff c => exact DegreeIn.coeff c
  | atom w a e ih => exact DegreeIn.other 0 w a (Ne.symm (Fin.succ_ne_zero j)) ih
  | add e f ihe ihf => exact DegreeIn.add ihe ihf

lemma coefficientDerivative_zero (i : Fin 7 × Fin 4) :
    coefficientDerivative (fun _ => 0) i = fun _ => 0 := by
  funext z
  simp [coefficientDerivative]

/-- Differentiating the base map adds exactly one occurrence of the chosen
variation slot to each monomial. -/
theorem DegreeIn.differentiate {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (h : DegreeIn j e n) (k : Fin 3) :
    DegreeIn j (e.differentiate k) (n + if k = j then 1 else 0) := by
  induction h with
  | coeff c =>
    apply degree_sumList
    intro i _
    by_cases hk : k = j
    · subst k
      simpa only [↓reduceIte, Nat.zero_add] using
        DegreeIn.same (j := j) (lowWord i.1) i.2 (DegreeIn.coeff (coefficientDerivative c i))
    · simpa only [hk, ↓reduceIte, Nat.zero_add] using
        DegreeIn.other k.succ (lowWord i.1) i.2 (by simpa using hk)
          (DegreeIn.coeff (coefficientDerivative c i))
  | zero n =>
    apply degree_sumList
    intro i _
    rw [coefficientDerivative_zero]
    by_cases hk : k = j
    · subst k
      simpa only [↓reduceIte] using
        DegreeIn.same (j := j) (lowWord i.1) i.2 (DegreeIn.zero n)
    · simpa only [hk, ↓reduceIte, Nat.add_zero] using
        DegreeIn.other k.succ (lowWord i.1) i.2 (by simpa using hk) (DegreeIn.zero n)
  | @other e n i w a hi h ih =>
    by_cases hi0 : i = 0
    · subst i
      simp only [MixedExpression.differentiate, ↓reduceIte]
      apply DegreeIn.add
      · by_cases hk : k = j
        · subst k
          simpa only [↓reduceIte] using DegreeIn.same w a h
        · simpa only [hk, ↓reduceIte, Nat.add_zero] using
            DegreeIn.other k.succ w a (by simpa using hk) h
      · exact DegreeIn.other 0 w a hi ih
    · simpa only [MixedExpression.differentiate, hi0, ↓reduceIte] using DegreeIn.other i w a hi ih
  | @same e n w a h ih =>
    simpa only [MixedExpression.differentiate, Fin.succ_ne_zero, ↓reduceIte, Nat.add_right_comm n 1]
      using DegreeIn.same w a ih
  | add he hf ihe ihf => exact DegreeIn.add ihe ihf

def scaleSlot (G : Fin 4 → Base → Space) (j : Fin 3) (c : ℝ) : Fin 4 → Base → Space :=
  fun i p => if i = j.succ then c • G i p else G i p

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual polynomial variations have one fixed scale
exponent, the excess-jet loss plus six. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace Expression

def variations (e : Expression) : Fin 3 → MixedExpression :=
  ![(ofExpression e).differentiate 0,
    ((ofExpression e).differentiate 0).differentiate 1,
    (((ofExpression e).differentiate 0).differentiate 1).differentiate 2]

lemma variations_smoothCoeffs {O : Set LowJet} (hO : IsOpen O)
    {e : Expression} (he : e.SmoothCoeffs O) (i : Fin 3) :
    (e.variations i).SmoothCoeffs O := by
  have h₀ := smoothCoeffs_ofExpression he
  have h₁ := differentiate_smoothCoeffs hO 0 h₀
  have h₂ := differentiate_smoothCoeffs hO 1 h₁
  have h₃ := differentiate_smoothCoeffs hO 2 h₂
  fin_cases i
  · exact h₁
  · exact h₂
  · exact h₃

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationScaling
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multilinear scaling of the three actual polynomial variations. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

namespace Expression

lemma variations_degree (e : Expression) (i j : Fin 3) :
    DegreeIn j (e.variations i) (if j ≤ i then 1 else 0) := by
  have h₀ := degree_ofExpression j e
  have h₁ := h₀.differentiate 0
  have h₂ := h₁.differentiate 1
  have h₃ := h₂.differentiate 2
  fin_cases i <;> fin_cases j <;> simp_all [variations]

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexMixedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex evaluation of the real polynomial variations, keeping the base
map fixed and complexifying the direction jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

abbrev JetData := Fin 4 → List (Fin 2) → Fin 4 → Base → ℂ

def evalComplex : MixedExpression → (Base → Space) → JetData → Base × ℝ → ℂ
  | .coeff c, G, _, z => (c (lowJet G z.1, z.2) : ℂ)
  | .atom i w a e, G, J, z => J i w a z.1 * e.evalComplex G J z
  | .add e f, G, J, z => e.evalComplex G J z + f.evalComplex G J z

def scaleJetSlot (J : JetData) (j : Fin 3) (c : Base → ℂ) : JetData :=
  fun i w a p => if i = j.succ then c p * J i w a p else J i w a p

lemma DegreeIn.evalComplex_scaleSlot {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (he : DegreeIn j e n) (G : Base → Space) (J : JetData) (c : Base → ℂ) (z : Base × ℝ) :
    e.evalComplex G (scaleJetSlot J j c) z = c z.1 ^ n * e.evalComplex G J z := by
  induction he with
  | coeff d => simp only [evalComplex, pow_zero, one_mul]
  | zero n => simp only [evalComplex, Complex.ofReal_zero, mul_zero]
  | other i w a hi h ih =>
    simp only [evalComplex, scaleJetSlot, hi, ↓reduceIte, ih]
    ring
  | same w a h ih =>
    simp only [evalComplex, scaleJetSlot, ↓reduceIte, ih, pow_succ]
    ring
  | add he hf ihe ihf => simp only [evalComplex, ihe, ihf, mul_add]

def scaleJets (J : JetData) (c : Fin 3 → Base → ℂ) : JetData :=
  scaleJetSlot (scaleJetSlot (scaleJetSlot J 0 (c 0)) 1 (c 1)) 2 (c 2)

lemma evalComplex_scaleJets {e : MixedExpression} {n : Fin 3 → ℕ}
    (he : ∀ j, DegreeIn j e (n j)) (G : Base → Space) (J : JetData)
    (c : Fin 3 → Base → ℂ) (z : Base × ℝ) :
    e.evalComplex G (scaleJets J c) z =
      ((c 0 z.1) ^ n 0 * (c 1 z.1) ^ n 1 * (c 2 z.1) ^ n 2) * e.evalComplex G J z := by
  simp only [scaleJets, (he 2).evalComplex_scaleSlot, (he 1).evalComplex_scaleSlot,
    (he 0).evalComplex_scaleSlot]
  ring

lemma evalComplex_smooth {O : Set LowJet} {U : Set Base} {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    {J : JetData} (hJ : ∀ i w a, ContDiffOn ℝ ∞ (J i w a) U)
    {e : MixedExpression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.evalComplex G J) (U ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      (he.comp (((lowJet_smooth hG).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
        (fun z hz => ⟨hQ hz.1, hz.2⟩))
  | atom i w a e ih =>
    exact ((hJ i w a).comp contDiffOn_fst (fun _ hz => hz.1)).mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

lemma evalComplex_parameter_smooth {O : Set LowJet} {U : Set Base} {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    {J : JetData} (hJ : ∀ i w a, ContDiffOn ℝ ∞ (J i w a) U)
    {e : MixedExpression} (he : e.SmoothCoeffs O) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun p => e.evalComplex G J (p, t)) U :=
  (evalComplex_smooth hG hQ hJ he).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun _ hp => ⟨hp, Set.mem_univ t⟩)

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ModulatedPolynomialJets
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual oscillatory direction jets factor into one phase per direction
and a slow amplitude jet. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace MixedExpression

lemma scaleJets_base (J : JetData) (c : Fin 3 → Base → ℂ) (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    scaleJets J c 0 w a p = J 0 w a p := by
  simp [scaleJets, scaleJetSlot]

lemma scaleJets_succ (J : JetData) (c : Fin 3 → Base → ℂ) (j : Fin 3)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    scaleJets J c j.succ w a p = c j p * J j.succ w a p := by
  fin_cases j <;> simp [scaleJets, scaleJetSlot]

end MixedExpression
namespace ModulatedJets

abbrev DirectionFields := Fin 3 → Base → Fin 4 → ℂ

def amplitudeData (G : Base → Space) (φ : Fin 3 → Base → ℝ)
    (H : DirectionFields) (τ : ℝ) : JetData :=
  Fin.cases (fun w a p => (jet G w a p : ℂ))
    (fun j w a => amplitudeJet τ (φ j) (w.map coordinateVector) (fun p => H j p a))

def oscillatoryData (G : Base → Space) (φ : Fin 3 → Base → ℝ)
    (H : DirectionFields) (τ : ℝ) : JetData :=
  Fin.cases (fun w a p => (jet G w a p : ℂ))
    (fun j w a => iteratedDirectional (w.map coordinateVector)
      (fun p => phase τ (φ j) p * H j p a))

lemma oscillatoryData_factor (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) :
    oscillatoryData G φ H τ = scaleJets (amplitudeData G φ H τ) (fun j => phase τ (φ j)) := by
  funext i w a p
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (scaleJets_base (amplitudeData G φ H τ) (fun j => phase τ (φ j)) w a p).symm
  · rw [scaleJets_succ]
    exact congrFun (iterated_phase_product (hφ j) (contDiff_pi.mp (hH j) a)
      τ (w.map coordinateVector)) p

lemma amplitudeData_smooth {G : Base → Space} {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hG : ContDiff ℝ ∞ G) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) :
    ∀ i w a, ContDiff ℝ ∞ (amplitudeData G φ H τ i w a) := by
  intro i w a
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Complex.ofRealCLM.contDiff.comp (jet_smooth hG w a)
  · exact amplitudeJet_smooth (hφ j) (contDiff_pi.mp (hH j) a) τ (w.map coordinateVector)

/-- Exact phase cancellation for each of the first three complexified
variations. The remaining factors are the modulated amplitude jets. -/
theorem variation_phase_factor (e : Expression) (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) (z : Base × ℝ) (i : Fin 3) :
    (e.variations i).evalComplex G (oscillatoryData G φ H τ) z =
      (phase τ (φ 0) z.1 * (if 1 ≤ i then phase τ (φ 1) z.1 else 1) *
        (if 2 ≤ i then phase τ (φ 2) z.1 else 1)) *
      (e.variations i).evalComplex G (amplitudeData G φ H τ) z := by
  rw [oscillatoryData_factor G hφ hH τ]
  have h := evalComplex_scaleJets (fun j => e.variations_degree i j) G
    (amplitudeData G φ H τ) (fun j => phase τ (φ j)) z
  fin_cases i <;> simpa using h

end ModulatedJets
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConjugatedVariationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp slow-scale estimates for the first three conjugated polynomial
variations. The power E+6 is independent of correction accuracy and order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

def phaseProduct (φ : Fin 3 → Base → ℝ) (τ : ℝ) (i : Fin 3) (p : Base) : ℂ :=
  phase τ (φ 0) p * (if 1 ≤ i then phase τ (φ 1) p else 1) *
    (if 2 ≤ i then phase τ (φ 2) p else 1)

lemma phaseProduct_ne_zero (φ : Fin 3 → Base → ℝ) (τ : ℝ) (i : Fin 3) (p : Base) :
    phaseProduct φ τ i p ≠ 0 := by
  have h (j : Fin 3) : phase τ (φ j) p ≠ 0 := Complex.exp_ne_zero _
  apply mul_ne_zero
  · exact mul_ne_zero (h 0) (by split_ifs; exact h 1; exact one_ne_zero)
  · split_ifs
    · exact h 2
    · exact one_ne_zero

def conjugatedVariation (e : Expression) (G : Base → Space)
    (φ : Fin 3 → Base → ℝ) (H : DirectionFields) (τ : ℝ) (i : Fin 3) (z : Base × ℝ) : ℂ :=
  (phaseProduct φ τ i z.1)⁻¹ * (e.variations i).evalComplex G (oscillatoryData G φ H τ) z

lemma conjugatedVariation_eq (e : Expression) (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) (i : Fin 3) (z : Base × ℝ) :
    conjugatedVariation e G φ H τ i z =
      (e.variations i).evalComplex G (amplitudeData G φ H τ) z := by
  rw [conjugatedVariation, variation_phase_factor e G hφ hH τ z i]
  change (phaseProduct φ τ i z.1)⁻¹ *
    (phaseProduct φ τ i z.1 * (e.variations i).evalComplex G (amplitudeData G φ H τ) z) = _
  rw [← mul_assoc, inv_mul_cancel₀ (phaseProduct_ne_zero φ τ i z.1), one_mul]

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial perturbations have one fixed short-scale exponent. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression ModulatedJets

variable {n : ℕ}

def conjugated (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : Fin 3 → Base → ℝ) (H : DirectionFields) (τ : ℝ) (i : Fin 3) (z : Base × ℝ) : ℂ :=
  ∑ l, ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i z

lemma conjugatedVariation_smooth {U : Set Base} {O : Set LowJet} {e : Expression}
    (he : e.SmoothCoeffs O) {G : Base → Space} {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (hO : IsOpen O)
    (hQ : Set.MapsTo (lowJet G) U O) (τ : ℝ) (i : Fin 3) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun p => conjugatedVariation e G φ H τ i (p, t)) U := by
  have h := evalComplex_parameter_smooth hG hQ
    (fun j w a => (amplitudeData_smooth hG hφ hH τ j w a).contDiffOn)
    (e := e.variations i) (e.variations_smoothCoeffs hO he i) t
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact conjugatedVariation_eq e G hφ hH τ i (p, t)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexJetDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and imaginary parts commute with all actual ordered jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma directional_clm {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : A → E} (hf : ContDiff ℝ ∞ f) (w : List A) :
    iteratedDirectional w (L ∘ f) = L ∘ iteratedDirectional w f := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    rw [iteratedDirectional, ih]
    funext p
    have hs := contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn w)
    exact congrArg (fun T : A →L[ℝ] F => T v)
      ((L.hasFDerivAt.comp p (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt).fderiv)

def complexJet (H : Base → Fin 4 → ℂ) (w : List (Fin 2)) (a : Fin 4) : Base → ℂ :=
  iteratedDirectional (w.map coordinateVector) (fun p => H p a)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexFirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complex polynomial first variation is exactly the complexification
of the actual real differential. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

def complexDirectionData (G : Base → Space) (H : Base → Fin 4 → ℂ) : JetData :=
  Fin.cases (fun w a p => (jet G w a p : ℂ))
    (fun j w a p => if j = 0 then complexJet H w a p else 0)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ConjugatedPolynomialOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The oscillatory estimates apply to the actual conjugated polynomial
linearization on supported smooth fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma iteratedDirectional_zero {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (w : List A) :
    iteratedDirectional w (fun _ : A => (0 : F)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons v w ih => simp [iteratedDirectional, ih]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the real polynomial linearization from the complex conjugated
operator. This is the realization identity needed by forced cancellation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

namespace Perturbation

def linearized {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G H : Base → Space)
    (t : ℝ) (p : Base) : ℝ := ∑ l, ε ^ (l.val + 1) * (P l).variation G H (p,t)

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexSlotAdditivity
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Additivity in each degree-one complex direction slot of the actual
mixed polynomial variation. -/
noncomputable section
namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

theorem degree_addition {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (he : DegreeIn j e n) (G : Base → Space) (J₁ J₂ J₃ : JetData) (z : Base × ℝ)
    (h₂ : ∀ i, i ≠ j.succ → ∀ w a, J₂ i w a z.1 = J₁ i w a z.1)
    (h₃ : ∀ i, i ≠ j.succ → ∀ w a, J₃ i w a z.1 = J₁ i w a z.1)
    (hadd : ∀ w a, J₃ j.succ w a z.1 = J₁ j.succ w a z.1 + J₂ j.succ w a z.1) :
    (n = 0 → e.evalComplex G J₁ z = e.evalComplex G J₂ z ∧
      e.evalComplex G J₃ z = e.evalComplex G J₁ z) ∧
    (n = 1 → e.evalComplex G J₃ z = e.evalComplex G J₁ z + e.evalComplex G J₂ z) := by
  induction he with
  | coeff c =>
    constructor
    · intro _; exact ⟨rfl, rfl⟩
    · intro hn; omega
  | zero k => simp [evalComplex]
  | other i w a hi h ih =>
    constructor
    · intro hn
      obtain ⟨h12, h31⟩ := ih.1 hn
      simp only [evalComplex, h₂ i hi, h₃ i hi, h12, h31, and_self]
    · intro hn
      simp only [evalComplex, h₂ i hi, h₃ i hi, ih.2 hn, mul_add]
  | @same e k w a h ih =>
    constructor
    · intro hn; omega
    · intro hn
      have hk : k = 0 := by omega
      obtain ⟨h12, h31⟩ := ih.1 hk
      simp only [evalComplex, hadd, h31, ← h12, add_mul]
  | add he hf ihe ihf =>
    constructor
    · intro hn
      obtain ⟨he12, he31⟩ := ihe.1 hn
      obtain ⟨hf12, hf31⟩ := ihf.1 hn
      simp only [evalComplex, he12, he31, hf12, hf31, and_self]
    · intro hn
      simp only [evalComplex, ihe.2 hn, ihf.2 hn]
      ring

theorem DegreeIn.evalComplex_add {j : Fin 3} {e : MixedExpression}
    (he : DegreeIn j e 1) (G : Base → Space) (J₁ J₂ J₃ : JetData) (z : Base × ℝ)
    (h₂ : ∀ i, i ≠ j.succ → ∀ w a, J₂ i w a z.1 = J₁ i w a z.1)
    (h₃ : ∀ i, i ≠ j.succ → ∀ w a, J₃ i w a z.1 = J₁ i w a z.1)
    (hadd : ∀ w a, J₃ j.succ w a z.1 = J₁ j.succ w a z.1 + J₂ j.succ w a z.1) :
    e.evalComplex G J₃ z = e.evalComplex G J₁ z + e.evalComplex G J₂ z :=
  (degree_addition he G J₁ J₂ J₃ z h₂ h₃ hadd).2 rfl

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexQuadraticVariation
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complexified second polynomial variation, with both direction
slots and their bilinear algebra made explicit. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

abbrev DirectionJets := List (Fin 2) → Fin 4 → Base → ℂ

def pairJetData (G : Base → Space) (J K : DirectionJets) : JetData :=
  ![fun w a p => (jet G w a p : ℂ), J, K, 0]

def quadraticComplex (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (z : Base × ℝ) : ℂ :=
  (e.variations 1).evalComplex G (pairJetData G J K) z

lemma quadraticComplex_add_left (e : Expression) (G : Base → Space)
    (J K L : DirectionJets) (z : Base × ℝ) :
    quadraticComplex e G (J + K) L z = quadraticComplex e G J L z + quadraticComplex e G K L z := by
  apply DegreeIn.evalComplex_add (j := 0)
    (show DegreeIn 0 (e.variations 1) 1 by simpa using e.variations_degree 1 0)
  · intro i hi w a
    fin_cases i <;> simp_all [pairJetData]
  · intro i hi w a
    fin_cases i <;> simp_all [pairJetData]
  · intro w a
    rfl

lemma quadraticComplex_add_right (e : Expression) (G : Base → Space)
    (J K L : DirectionJets) (z : Base × ℝ) :
    quadraticComplex e G J (K + L) z = quadraticComplex e G J K z + quadraticComplex e G J L z := by
  apply DegreeIn.evalComplex_add (j := 1)
    (show DegreeIn 1 (e.variations 1) 1 by simpa using e.variations_degree 1 1)
  · intro i hi w a
    fin_cases i <;> simp_all [pairJetData]
  · intro i hi w a
    fin_cases i <;> simp_all [pairJetData]
  · intro w a
    rfl

lemma quadraticComplex_smul_left (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (c : ℂ) (z : Base × ℝ) :
    quadraticComplex e G (c • J) K z = c * quadraticComplex e G J K z := by
  have hh := (show DegreeIn 0 (e.variations 1) 1 by simpa using e.variations_degree 1 0).evalComplex_scaleSlot
    G (pairJetData G J K) (fun _ => c) z
  have he : scaleJetSlot (pairJetData G J K) 0 (fun _ => c) = pairJetData G (c • J) K := by
    funext i w a p
    fin_cases i <;> simp [scaleJetSlot, pairJetData]
  rw [he, pow_one] at hh
  exact hh

lemma quadraticComplex_smul_right (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (c : ℂ) (z : Base × ℝ) :
    quadraticComplex e G J (c • K) z = c * quadraticComplex e G J K z := by
  have hh := (show DegreeIn 1 (e.variations 1) 1 by simpa using e.variations_degree 1 1).evalComplex_scaleSlot
    G (pairJetData G J K) (fun _ => c) z
  have he : scaleJetSlot (pairJetData G J K) 1 (fun _ => c) = pairJetData G J (c • K) := by
    funext i w a p
    fin_cases i <;> simp [scaleJetSlot, pairJetData]
  rw [he, pow_one] at hh
  exact hh

def starDirectionJets (J : DirectionJets) : DirectionJets := fun w a p => star (J w a p)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialQuadraticPhases
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact zero- and double-phase terms of the polynomial Hessian. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

def pairPhases (φ ψ : Base → ℝ) : Fin 3 → Base → ℝ := ![φ, ψ, 0]
def pairDirections (H K : Base → Fin 4 → ℂ) : DirectionFields := ![H, K, 0]
def starField (H : Base → Fin 4 → ℂ) : Base → Fin 4 → ℂ := fun p a => star (H p a)

lemma starField_smooth {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (starField H) := by
  apply contDiff_pi.mpr
  intro a
  exact Complex.conjCLE.contDiff.comp (contDiff_pi.mp hH a)

lemma complexJet_starField {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) :
    complexJet (starField H) = starDirectionJets (complexJet H) := by
  funext w a p
  exact congrFun (directional_clm Complex.conjCLE.toContinuousLinearMap
    (contDiff_pi.mp hH a) (w.map coordinateVector)) p

lemma phase_star (τ : ℝ) (φ : Base → ℝ) (p : Base) :
    star (phase τ φ p) = phase τ (fun q => -φ q) p := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul, map_div₀,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  congr 1
  ring

lemma starField_phase (τ : ℝ) (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) :
    starField (fun p => phase τ φ p • H p) =
      fun p => phase τ (fun q => -φ q) p • starField H p := by
  funext p a
  simp only [starField, Pi.smul_apply, smul_eq_mul, star_mul', phase_star]

lemma pair_oscillatoryData (G : Base → Space) (φ ψ : Base → ℝ)
    (H K : Base → Fin 4 → ℂ) (τ : ℝ) :
    oscillatoryData G (pairPhases φ ψ) (pairDirections H K) τ =
      pairJetData G (complexJet (fun p => phase τ φ p • H p))
        (complexJet (fun p => phase τ ψ p • K p)) := by
  funext i w a p
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change iteratedDirectional (w.map coordinateVector)
      (fun p => phase τ (fun _ => 0) p * (0 : ℂ)) p = 0
    simp only [mul_zero, iteratedDirectional_zero]

lemma quadraticComplex_phase_factor (e : Expression) (G : Base → Space) (φ ψ : Base → ℝ)
    (H K : Base → Fin 4 → ℂ) (τ : ℝ) (z : Base × ℝ) :
    quadraticComplex e G (complexJet (fun p => phase τ φ p • H p))
        (complexJet (fun p => phase τ ψ p • K p)) z =
      (phase τ φ z.1 * phase τ ψ z.1) *
        conjugatedVariation e G (pairPhases φ ψ) (pairDirections H K) τ 1 z := by
  have he : phaseProduct (pairPhases φ ψ) τ 1 z.1 = phase τ φ z.1 * phase τ ψ z.1 := by
    simp [phaseProduct, pairPhases]
  rw [quadraticComplex, ← pair_oscillatoryData, conjugatedVariation, ← he, ← mul_assoc,
    mul_inv_cancel₀ (phaseProduct_ne_zero _ _ _ _), one_mul]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial contribution to the quadratic zero-phase coefficient. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma pairPhases_smooth {φ ψ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) :
    ∀ j, ContDiff ℝ ∞ (pairPhases φ ψ j) := by
  intro j
  fin_cases j
  · exact hφ
  · exact hψ
  · exact contDiff_const

lemma pairDirections_smooth {H K : Base → Fin 4 → ℂ}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) :
    ∀ j, ContDiff ℝ ∞ (pairDirections H K j) := by
  intro j
  fin_cases j
  · exact hH
  · exact hK
  · exact contDiff_const

namespace Perturbation

def quadraticMeanCoefficient {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) : ℝ :=
  (conjugated P ε G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField H)) τ 1 (p, t)).re / 4

lemma quadraticMeanCoefficient_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    {G : Base → Space} {φ : Base → ℝ} {H : Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (hQ : Set.MapsTo (lowJet G) U O) (ε τ t : ℝ) :
    ContDiffOn ℝ ∞ (quadraticMeanCoefficient P ε G φ H τ t) U := by
  have hs := fun l => conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hφ.neg)
    (pairDirections_smooth hH (starField_smooth hH)) hO hQ τ 1 t
  exact (Complex.reCLM.contDiff.comp_contDiffOn
    (ContDiffOn.sum fun l _ => (hs l).const_smul (ε ^ (l.val + 1)))).div_const 4

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteQuadraticVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sums in the actual complexified Hessian. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

def quadraticComplexBilinear (e : Expression) (G : Base → Space) (z : Base × ℝ) :
    DirectionJets →ₗ[ℂ] DirectionJets →ₗ[ℂ] ℂ where
  toFun J := {
    toFun := fun K => quadraticComplex e G J K z
    map_add' := fun K L => quadraticComplex_add_right e G J K L z
    map_smul' := fun c K => quadraticComplex_smul_right e G J K c z }
  map_add' J K := by
    ext L
    exact quadraticComplex_add_left e G J K L z
  map_smul' c J := by
    ext K
    exact quadraticComplex_smul_left e G J K c z

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear form underlying the polynomial zero-phase correction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

lemma quadraticComplex_opposite_phases (e : Expression) (G : Base → Space)
    {φ : Base → ℝ} {H K : Base → Fin 4 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hK : ContDiff ℝ ∞ K) (τ : ℝ) (z : Base × ℝ) :
    quadraticComplex e G (complexJet (fun p => phase τ φ p • H p))
      (starDirectionJets (complexJet (fun p => phase τ φ p • K p))) z =
      conjugatedVariation e G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) τ 1 z := by
  have hsm : ContDiff ℝ ∞ (fun p => phase τ φ p • K p) := (phase_smooth hφ τ).smul hK
  rw [← complexJet_starField hsm, starField_phase, quadraticComplex_phase_factor,
    phase_neg_inv, mul_inv_cancel₀ (show phase τ φ z.1 ≠ 0 from Complex.exp_ne_zero _), one_mul]

namespace Perturbation

def quadraticMeanPair {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : Base → ℝ) (H K : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) : ℝ :=
  ∑ l, ε ^ (l.val + 1) *
    (quadraticComplex (P l) G (complexJet (fun p => phase τ φ p • H p))
      (starDirectionJets (complexJet (fun p => phase τ φ p • K p))) (p, t)).re / 4

lemma quadraticMeanPair_self {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) {H : Base → Fin 4 → ℂ}
    (hH : ContDiff ℝ ∞ H) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ H H τ t p = quadraticMeanCoefficient P ε G φ H τ t p := by
  simp only [quadraticMeanPair, quadraticComplex_opposite_phases _ G hφ hH,
    quadraticMeanCoefficient, conjugated, Complex.re_sum, Complex.real_smul,
    Finset.sum_div, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual polynomial quadratic mean preserves amplitude support, so
local smoothness near the support suffices for a global smooth coefficient. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma MixedExpression.evalComplex_congr (e : MixedExpression) (G : Base → Space)
    (J K : JetData) (z : Base × ℝ)
    (h : ∀ i w a, J i w a z.1 = K i w a z.1) :
    e.evalComplex G J z = e.evalComplex G K z := by
  induction e with
  | coeff c => rfl
  | atom i w a e ih => simp only [evalComplex, h, ih]
  | add e f ihe ihf => simp only [evalComplex, ihe, ihf]

lemma quadraticComplex_zero_at (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (z : Base × ℝ) (hJ : ∀ w a, J w a z.1 = 0) :
    quadraticComplex e G J K z = 0 := by
  have he : quadraticComplex e G J K z = quadraticComplex e G 0 K z := by
    apply MixedExpression.evalComplex_congr
    intro i w a
    fin_cases i
    · rfl
    · exact hJ w a
    · rfl
    · rfl
  rw [he]
  change quadraticComplexBilinear e G z 0 K = 0
  rw [map_zero, LinearMap.zero_apply]

lemma complexJet_zero_of_notMem {H : Base → Fin 4 → ℂ} {p : Base}
    (hp : p ∉ tsupport H) (w : List (Fin 2)) (a : Fin 4) : complexJet H w a p = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun hx => hp (((tsupport_iteratedDirectional (w.map coordinateVector) (fun p => H p a)).trans
    (tsupport_comp_subset (g := fun v : Fin 4 → ℂ => v a) rfl H)) hx)

namespace Perturbation

lemma quadraticMeanPair_zero_of_notMem {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ : Base → ℝ) (H J : Base → Fin 4 → ℂ)
    (τ t : ℝ) {p : Base} (hp : p ∉ tsupport H) :
    quadraticMeanPair P ε G φ H J τ t p = 0 := by
  have hp' : p ∉ tsupport (fun x => phase τ φ x • H x) :=
    fun hx => hp (tsupport_smul_subset_right (phase τ φ) H hx)
  apply Finset.sum_eq_zero
  intro l _
  rw [quadraticComplex_zero_at (P l) G _ _ (p, t)
    (fun w a => complexJet_zero_of_notMem hp' w a)]
  simp only [Complex.zero_re, mul_zero, zero_div]

lemma quadraticMeanPair_tsupport {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ : Base → ℝ) (H J : Base → Fin 4 → ℂ) (τ t : ℝ) :
    tsupport (quadraticMeanPair P ε G φ H J τ t) ⊆ tsupport H := by
  apply closure_minimal _ (isClosed_tsupport H)
  intro p hp
  by_contra hn
  exact hp (quadraticMeanPair_zero_of_notMem P ε G φ H J τ t hn)

lemma quadraticMeanCoefficient_tsupport {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (τ t : ℝ) :
    tsupport (quadraticMeanCoefficient P ε G φ H τ t) ⊆ tsupport H := by
  have he : quadraticMeanCoefficient P ε G φ H τ t = quadraticMeanPair P ε G φ H H τ t := by
    funext p
    exact (quadraticMeanPair_self P ε G hφ hH τ t p).symm
  rw [he]
  exact quadraticMeanPair_tsupport P ε G φ H H τ t

def polynomialMeanField {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (hP : ∀ l, (P l).SmoothCoeffs O) {G : Base → Space} {φ : Base → ℝ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (H : SupportedField (F := Fin 4 → ℂ) K) (ε τ t : ℝ) : SupportedField (F := ℝ) K :=
  let hs := (quadraticMeanCoefficient_tsupport P ε G hφ H.contDiff τ t).trans H.tsupport_subset
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset hU (hs.trans hKU)
      (quadraticMeanCoefficient_smooth hO hP hG hφ H.contDiff hQ ε τ t))
    (subset_closure.trans hs)

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialZeroPhaseExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the actual polynomial Hessian into its zero-phase part and
explicit doubled and mixed phases. Ordered pairs retain all multiplicities. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets
namespace Perturbation

def quadraticPhaseCoefficient {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ ψ : Base → ℝ) (H K : Base → Fin 4 → ℂ)
    (τ t : ℝ) (p : Base) : ℂ :=
  conjugated P ε G (pairPhases φ ψ) (pairDirections H K) τ 1 (p, t) / 4

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPhaseSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every polynomial quadratic phase coefficient is smooth and supported
in the intersection of its two amplitude supports. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets WeightedEstimates

lemma quadraticComplex_zero_right_at (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (z : Base × ℝ) (hK : ∀ w a, K w a z.1 = 0) :
    quadraticComplex e G J K z = 0 := by
  have he : quadraticComplex e G J K z = quadraticComplex e G J 0 z := by
    apply MixedExpression.evalComplex_congr
    intro i w a
    fin_cases i
    · rfl
    · rfl
    · exact hK w a
    · rfl
  rw [he]
  change quadraticComplexBilinear e G z J 0 = 0
  exact map_zero _

namespace Perturbation

lemma quadraticPhaseCoefficient_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    {G : Base → Space} {φ ψ : Base → ℝ} {H K : Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (hQ : Set.MapsTo (lowJet G) U O) (ε τ t : ℝ) :
    ContDiffOn ℝ ∞ (quadraticPhaseCoefficient P ε G φ ψ H K τ t) U := by
  exact (ContDiffOn.sum fun l _ =>
    (conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hψ)
      (pairDirections_smooth hH hK) hO hQ τ 1 t).const_smul _).div_const 4

lemma quadraticPhaseCoefficient_zero_of_notMem {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ ψ : Base → ℝ) (H K : Base → Fin 4 → ℂ)
    (τ t : ℝ) {p : Base} (hp : p ∉ tsupport H ∩ tsupport K) :
    quadraticPhaseCoefficient P ε G φ ψ H K τ t p = 0 := by
  have hz (l : Fin n) : conjugatedVariation (P l) G (pairPhases φ ψ)
      (pairDirections H K) τ 1 (p,t) = 0 := by
    have hn : phase τ φ p * phase τ ψ p ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    have he : quadraticComplex (P l) G (complexJet (fun x => phase τ φ x • H x))
        (complexJet (fun x => phase τ ψ x • K x)) (p,t) = 0 := by
      by_cases hH : p ∈ tsupport H
      · have hK : p ∉ tsupport K := fun hk => hp ⟨hH, hk⟩
        have hk : p ∉ tsupport (fun x => phase τ ψ x • K x) :=
          fun hx => hK (tsupport_smul_subset_right (phase τ ψ) K hx)
        exact quadraticComplex_zero_right_at (P l) G _ _ _
          (fun w a => complexJet_zero_of_notMem hk w a)
      · have hh : p ∉ tsupport (fun x => phase τ φ x • H x) :=
          fun hx => hH (tsupport_smul_subset_right (phase τ φ) H hx)
        exact quadraticComplex_zero_at (P l) G _ _ _
          (fun w a => complexJet_zero_of_notMem hh w a)
    rw [quadraticComplex_phase_factor] at he
    exact (mul_eq_zero.mp he).resolve_left hn
  simp only [quadraticPhaseCoefficient, conjugated, hz, smul_zero, Finset.sum_const_zero,
    zero_div]

lemma quadraticPhaseCoefficient_tsupport {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ ψ : Base → ℝ) (H K : Base → Fin 4 → ℂ) (τ t : ℝ) :
    tsupport (quadraticPhaseCoefficient P ε G φ ψ H K τ t) ⊆ tsupport H ∩ tsupport K := by
  apply closure_minimal _ ((isClosed_tsupport H).inter (isClosed_tsupport K))
  intro p hp
  by_contra hn
  exact hp (quadraticPhaseCoefficient_zero_of_notMem P ε G φ ψ H K τ t hn)

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialQuadraticFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Index the polynomial quadratic remainder by the same doubled and
mixed labels used for the metric quadratic remainder. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open ModulatedJets

def quadraticFamilyPhase {ι : Type*} (φ : ι → Base → ℝ) :
    RealModes.QuadraticLabel ι → Base → ℝ
  | .inl i => fun p => 2 * φ i p
  | .inr ⟨i, j, b⟩ => if b then (fun p => φ i p - φ j p) else (fun p => φ i p + φ j p)

def quadraticFamilyCoefficient {n : ℕ} {ι : Type*}
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) :
    RealModes.QuadraticLabel ι → Base → ℂ
  | .inl i => quadraticPhaseCoefficient P ε G (φ i) (φ i) (H i) (H i) τ t
  | .inr ⟨i, j, b⟩ => if b then
      quadraticPhaseCoefficient P ε G (φ i) (fun p => -φ j p) (H i) (starField (H j)) τ t
    else quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t

def quadraticFamilySupport {ι : Type*} (S : ι → Set Base) :
    RealModes.QuadraticLabel ι → Set Base
  | .inl i => S i
  | .inr ⟨i, j, _⟩ => S i ∩ S j

lemma starField_tsupport (H : Base → Fin 4 → ℂ) : tsupport (starField H) ⊆ tsupport H := by
  apply closure_minimal _ (isClosed_tsupport H)
  intro p hp
  by_contra hn
  apply hp
  funext a
  simp only [starField, image_eq_zero_of_notMem_tsupport hn, Pi.zero_apply, star_zero]

lemma quadraticFamilyCoefficient_tsupport {n : ℕ} {ι : Type*}
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    {S : ι → Set Base} (hH : ∀ i, tsupport (H i) ⊆ S i) :
    ∀ l, tsupport (quadraticFamilyCoefficient P ε G φ H τ t l) ⊆ quadraticFamilySupport S l := by
  intro l
  rcases l with i | ⟨i,j,b⟩
  · exact (quadraticPhaseCoefficient_tsupport P ε G (φ i) (φ i) (H i) (H i) τ t).trans
      (fun _ hp => hH i hp.1)
  · cases b
    · exact (quadraticPhaseCoefficient_tsupport P ε G (φ i) (φ j) (H i) (H j) τ t).trans
        (Set.inter_subset_inter (hH i) (hH j))
    · exact (quadraticPhaseCoefficient_tsupport P ε G (φ i) (fun p => -φ j p)
        (H i) (starField (H j)) τ t).trans
        (Set.inter_subset_inter (hH i) ((starField_tsupport (H j)).trans (hH j)))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedPolynomialMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial part of the normalized quadratic mean is O(η), with
finite-loss value and difference bounds and constants chosen before scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

def normalizedPolynomialMean {n : ℕ} (P : Fin n → Expression) (δ ε : ℝ)
    (G : Base → Space) (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ t : ℝ) : Base → ℝ :=
  fun p => δ⁻¹ ^ 2 * quadraticMeanCoefficient P ε G φ H τ t p

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedPolynomialSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support and global smoothness of the normalized polynomial mean. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma normalizedPolynomialMean_tsupport {n : ℕ} (P : Fin n → Expression) (δ ε : ℝ)
    (G : Base → Space) {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (τ t : ℝ) :
    tsupport (normalizedPolynomialMean P δ ε G φ H τ t) ⊆ tsupport H :=
  tsupport_mul_subset_right.trans (quadraticMeanCoefficient_tsupport P ε G hφ hH τ t)

lemma normalizedPolynomialMean_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (hP : ∀ l, (P l).SmoothCoeffs O) {G : Base → Space} {φ : Base → ℝ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (H : SupportedField (F := Fin 4 → ℂ) K) (δ ε τ t : ℝ) :
    ContDiff ℝ ∞ (normalizedPolynomialMean P δ ε G φ H τ t) := by
  exact ((polynomialMeanField hU hO hP hG hφ hQ K hKU H ε τ t).contDiff).const_smul (δ⁻¹ ^ 2)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialQuadraticTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth supported tensor targets for every polynomial quadratic phase. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma quadraticFamilyCoefficient_smooth {n : ℕ} {ι : Type*}
    {P : Fin n → Expression} {U : Set Base} {O : Set LowJet}
    (hO : IsOpen O) (hP : ∀ j, (P j).SmoothCoeffs O) {G : Base → Space}
    {φ : ι → Base → ℝ} {H : ι → Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (hQ : Set.MapsTo (lowJet G) U O)
    (ε τ t : ℝ) (l : RealModes.QuadraticLabel ι) :
    ContDiffOn ℝ ∞ (quadraticFamilyCoefficient P ε G φ H τ t l) U := by
  rcases l with i | ⟨i,j,b⟩
  · exact quadraticPhaseCoefficient_smooth hO hP hG (hφ i) (hφ i) (hH i) (hH i) hQ ε τ t
  · cases b
    · exact quadraticPhaseCoefficient_smooth hO hP hG (hφ i) (hφ j) (hH i) (hH j) hQ ε τ t
    · exact quadraticPhaseCoefficient_smooth hO hP hG (hφ i) (hφ j).neg
        (hH i) (starField_smooth (hH j)) hQ ε τ t

def quadraticFamilyTensor {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    (l : RealModes.QuadraticLabel ι) : Base → Fin 3 → ℂ :=
  fun x k => quadraticFamilyCoefficient (P k) ε G φ H τ t l x

lemma quadraticFamilyTensor_tsupport {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    {S : ι → Set Base} (hS : ∀ i, IsClosed (S i)) (hH : ∀ i, tsupport (H i) ⊆ S i)
    (l : RealModes.QuadraticLabel ι) :
    tsupport (quadraticFamilyTensor P ε G φ H τ t l) ⊆ quadraticFamilySupport S l := by
  have hclosed : IsClosed (quadraticFamilySupport S l) := by
    rcases l with i | ⟨i,j,b⟩
    · exact hS i
    · exact (hS i).inter (hS j)
  apply closure_minimal _ hclosed
  intro x hx
  by_contra hn
  apply hx
  funext k
  change quadraticFamilyCoefficient (P k) ε G φ H τ t l x = 0
  exact image_eq_zero_of_notMem_tsupport (fun hp => hn
    (quadraticFamilyCoefficient_tsupport (P k) ε G φ H τ t hH l hp))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorPlaneReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction from the three independent tensor coordinates. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean
open JetPolynomial (Base planeCoordinateIsometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance reconstructionFiberNormed_r34e91d_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance reconstructionFiberSpace_r34e91d_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance reconstructionDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean substitution on actual global tensor sections, represented
by redundant atlas coordinates. Every iterate stays in the representation
range, so no leading-identity premise on arbitrary plane fields is needed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance iterationModelNormed : NormedAddCommGroup TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.iterationDualAdd
local instance iterationModelSpace_r34e91d_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance iterationDualSmul_r34e91d_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance iterationSectionTensorNormed_r34e91d_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance iterationSectionTensorSpace_r34e91d_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorDecodeLM : (Base → A.centers → TensorFiber) →ₗ[ℝ] (∀ x : M, CovariantTwoTensor x) where
  toFun := A.tensorDecode
  map_add' := A.tensorDecode_add
  map_smul' := A.tensorDecode_smul

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorDecodedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform chart-reading estimates for the redundant coordinates used by
finite mean substitution, including the radius of every local trial ball. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance decodedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance decodedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance decodedDualAdd_r34e91d_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance decodedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorAtlasMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global nonlinear mean is the finite restoration of the actual
local means evaluated on unweighted chart readings. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance atlasMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasMeanDualAdd_r34e91d_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothedInputAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-norm bootstrap assumptions imply the actual smoothed inputs
remain inside the fixed map and tensor neighborhoods. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

local instance admissibilityFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance admissibilityFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactSectionBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every smooth input has finite bounds at each fixed atlas order. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_smooth_bound {f : Base → F} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ WeightedBound univ 1 m C f := by
  classical
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C :=
    (hc.iteratedFDeriv j).exists_bound_of_continuous (hf.continuous_iteratedFDeriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  choose C hC using hb
  refine ⟨∑ j ∈ Finset.range (m + 1), |C j|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro j hj x _
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ]
  exact ((hC j x).trans (le_abs_self _)).trans
    (Finset.single_le_sum (s := Finset.range (m + 1)) (a := j)
      (fun k _ => abs_nonneg (C k)) (Finset.mem_range.mpr (by omega)))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialDiagonalVariations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual parameter derivatives of a polynomial along a
map variation are its mixed variations with all directions equal. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression SmoothPeriodicCalculus

def diagonalFamily (G H : Base → Space) : Fin 4 → Base → Space :=
  Fin.cases G (fun _ => H)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTaylorRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted cubic estimate for the actual higher-jet polynomial map. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open MixedExpression SmoothParameterIntegral WeightedEstimates

def taylorRemainder (e : Expression) (G H : Base → Space) (θ : ℝ) (p : Base) : ℝ :=
  e.eval (fun q => G q + H q) (p, θ) - e.eval G (p, θ) - e.variation G H (p, θ) -
    (1 / 2 : ℝ) * (e.variations 1).eval (diagonalFamily G H) (p, θ)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasFreeOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global free oscillation and its weighted displacement bound. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance atlasFreeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasFreeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasFreeDualAdd_r34e91d_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasFreeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalOscillatoryModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global phase/amplitude representatives of the actual supported oscillations. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

def surfaceMode {X : Type*} {n : ℕ} (τ : ℝ) (φ : X → ℝ) (Z : X → Fin n → ℂ) :
    X → Fin n → ℝ := fun p => realMode (φ p/τ) (Z p)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorRestoreFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-sum linearity of the actual tensor restoration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance tensorRestoreFiniteFiberNormed_r34e91d_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorRestoreFiniteFiberSpace_r34e91d_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance tensorRestoreFiniteDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ActualSmoothedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual metric-adapted immersion supplies all the small-increment geometry. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
local instance actualSmoothedStepFiberNormed_r34e91d_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance actualSmoothedStepFiberSpace_r34e91d_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance actualSmoothedStepDualAdd_r34e91d_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance actualSmoothedStepDualSmul_r34e91d_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

/-- The explicit normalized metric error of a constructed step. Its
dependence on the uncontrolled input norm `C` is linear. -/
def normalizedStepBound (r q : ℕ) (B₀ D E V W C δ δ' τ s t : ℝ) : ℝ :=
  (δ'^2)⁻¹ * ((δ^2 + E*(V*(δ*τ))/τ) *
    (D*tailConstant r*(B₀*(s/t)^r+C*(τ/t)^r)) +
      W*(δ*(τ/s)^(q+1)+δ^3/τ))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialOperations
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

def fluct (e : Expression) : Expression := e.sub e.mean

@[simp] lemma order_neg (e : Expression) : e.neg.order = e.order := order_mapCoeff _ _
@[simp] lemma loss_neg (e : Expression) : e.neg.loss = e.loss := loss_mapCoeff _ _
@[simp] lemma order_sub (e f : Expression) : (e.sub f).order = max e.order f.order := by
  simp only [sub, order, order_neg]
@[simp] lemma loss_sub (e f : Expression) : (e.sub f).loss = max e.loss f.loss := by
  simp only [sub, loss, loss_neg]
@[simp] lemma order_fluct (e : Expression) : e.fluct.order = e.order := by
  simp only [fluct, order_sub, order_mean, max_self]
@[simp] lemma loss_fluct (e : Expression) : e.fluct.loss = e.loss := by
  simp only [fluct, loss_sub, loss_mean, max_self]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilies
attribute [-simp] _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def smoothFamilies : Submodule ℝ (A → C(Period, E)) where
  carrier := {F | ContDiffOn ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))
    ((O : Set A) ×ˢ Set.univ) ∧ ∀ p, p ∉ O → F p = 0}
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    exact ⟨hF.add hG, fun p hp => by change F p + G p = 0; rw [hF0 p hp, hG0 p hp, add_zero]⟩
  smul_mem' := by
    rintro c F ⟨hF, hF0⟩
    exact ⟨contDiffOn_const.smul hF, fun p hp => by change c • F p = 0; rw [hF0 p hp, smul_zero]⟩

def Family := ↥(smoothFamilies O E)
instance instAddCommGroupFamily : AddCommGroup (Family O E) := inferInstanceAs (AddCommGroup ↥(smoothFamilies O E))
instance instModuleRealFamily : Module ℝ (Family O E) := inferInstanceAs (Module ℝ ↥(smoothFamilies O E))

variable {O E}
namespace Family

def val (F : Family O E) : A → C(Period, E) := F.1
lemma smooth (F : Family O E) :
    ContDiffOn ℝ ∞ (fun z : A × ℝ => F.val z.1 (z.2 : Period))
      ((O : Set A) ×ˢ Set.univ) := F.2.1
lemma outside (F : Family O E) {p : A} (hp : p ∉ O) : F.val p = 0 := F.2.2 p hp

@[ext] lemma ext {F G : Family O E} (h : ∀ p ∈ O, ∀ t, F.val p t = G.val p t) : F = G := by
  apply Subtype.ext
  funext p
  by_cases hp : p ∈ O
  · exact ContinuousMap.ext (h p hp)
  · exact (F.outside hp).trans (G.outside hp).symm

@[simp] lemma zero_apply (p : A) (t : Period) : (0 : Family O E).val p t = 0 := rfl
@[simp] lemma add_apply (F G : Family O E) (p : A) (t : Period) :
    (F + G).val p t = F.val p t + G.val p t := rfl
@[simp] lemma sub_apply (F G : Family O E) (p : A) (t : Period) :
    (F - G).val p t = F.val p t - G.val p t := rfl
@[simp] lemma neg_apply (F : Family O E) (p : A) (t : Period) :
    (-F).val p t = -F.val p t := rfl
@[simp] lemma smul_apply (c : ℝ) (F : Family O E) (p : A) (t : Period) :
    (c • F).val p t = c • F.val p t := rfl
@[simp] lemma sum_apply {ι : Type*} (s : Finset ι) (F : ι → Family O E)
    (p : A) (t : Period) : (∑ i ∈ s, F i).val p t = ∑ i ∈ s, (F i).val p t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar polynomial representations of the finite metric coefficients. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion CovarianceCorrector

def scale (a : ℝ) (e : Expression) : Expression :=
  e.mapCoeff (fun c z => a * c z)

@[simp] lemma order_scale (a : ℝ) (e : Expression) : (e.scale a).order = e.order := order_mapCoeff _ _
@[simp] lemma loss_scale (a : ℝ) (e : Expression) : (e.scale a).loss = e.loss := loss_mapCoeff _ _

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionApproximation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing a compact C1 immersion while keeping its differential injective. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def coreThreshold : ℝ := 1 / ((Fintype.card A.centers : ℝ)+1)
def weightCore (i : A.centers) : Set M := {p | A.coreThreshold ≤ (A.weight i p)^2}
def coordinateCore (i : A.centers) : Set Base := (chart (i : M)) '' A.weightCore i

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_EuclideanRestoration
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore a compactly supported Euclidean chart correction. The support
and germ formulas are used in finite-point spherical preparation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def euclideanRestore (p : M) (χ : M → ℝ) (h : Plane → Space) : M → Space :=
  restore p χ (h ∘ (EuclideanSpace.equiv (Fin 2) ℝ).symm)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteSingularProjection
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual smooth map of every compact surface into three-space with
only finitely many singular points. The regularity of its direction
parameter maps is retained for the subsequent local analysis. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def projectionJet (F : M → ProjectionTarget 3 × ℝ) (i : A.centers) :
    Base → Base →L[ℝ] ProjectionTarget 3 × ℝ :=
  weightedJet (localizedWeight (i : M) (A.weight i)) (localize (i : M) (A.weight i) F)

end SmoothingAtlas

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceDirectionJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative-direction map of an actual three-dimensional surface,
and its relation to the unweighted projection jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def surfaceDirection (f : Base → ProjectionTarget 3) (b : Bool)
    (z : Base × ℝ) : ProjectionTarget 3 := fderiv ℝ f z.1 (tangentRay b z.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceQuadraticTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual second Taylor polynomial of a smooth surface map at the
coordinate origin, including exact vanishing jets of its remainder. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def surfaceQuadratic (B : Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) (x : Base) :
    ProjectionTarget 3 := (1/2 : ℝ) • B x x

def surfaceTaylorTwo (f : Base → ProjectionTarget 3) (x : Base) : ProjectionTarget 3 :=
  f 0+fderiv ℝ f 0 x+surfaceQuadratic (fderiv ℝ (fderiv ℝ f) 0) x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CenteredCrosscapPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local polynomial preparation centered at the actual chart
coordinate of a singular point. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def translatedSurface (f : Base → ProjectionTarget 3) (a : Base) : Base → ProjectionTarget 3 :=
  fun x => f (x+a)

def centeredSurfaceTaylor (f : Base → ProjectionTarget 3) (a : Base) (x : Base) : ProjectionTarget 3 :=
  surfaceTaylorTwo (translatedSurface f a) (x-a)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FixedSurfacePairPatch
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair patches and their cutoffs are fixed before the surface map or
perturbation size. Whole closed crosscap neighborhoods may be frozen. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

structure SurfacePairTranslationPatch (p q : M) where
  χ : M → ℝ
  smooth : ContMDiff planeModel 𝓘(ℝ) ∞ χ
  bounds : ∀ x, χ x ∈ Icc 0 1
  U : Set M
  V : Set M
  openU : IsOpen U
  openV : IsOpen V
  memU : p ∈ U
  memV : q ∈ V
  sourceU : closure U ⊆ (chart p).source
  sourceV : closure V ⊆ (chart q).source
  oneOn : EqOn χ 1 U
  zeroOn : EqOn χ 0 V

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FrozenTranslationGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation germs on frozen closed neighborhoods are retained by
finite compositions of the constructed scalar translation families. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M]

def FrozenTranslationGerms (A : ι → Set M) (f g : M → ProjectionTarget 3) : Prop :=
  ∀ i, ∃ c : ProjectionTarget 3, g =ᶠ[𝓝ˢ (A i)] (fun x => f x+c)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InputSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite joint input norms for the adaptive correction iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
local instance inputSizeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputSizeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticCrosscapFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nondegenerate quadratic crosscap is a standard umbrella followed
by a target map whose derivative at the origin is invertible. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

local instance tripleNormed_r34e91d_1 : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance tripleSpace_r34e91d_1 : NormedSpace ℝ (Base × ℝ) := inferInstance
/-- Standard umbrella, with the regular coordinate placed last. -/
def standardCrosscap (x : Base) : Base × ℝ := (![x 0*x 1,(x 1)^2],x 0)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneComplexFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real coordinate frame from a nonzero vector in the normal plane. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeComplexFrame (w : Base) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj 0).smulRight w+
    (ContinuousLinearMap.proj 1).smulRight ![-w 1,w 0]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceInjectivityPatch
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed coordinate balls with quantitative local injectivity margins. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

structure SurfaceInjectivityPatch (f : M → ProjectionTarget 3) (p : M) where
  radius : ℝ
  radius_pos : 0 < radius
  target : closedBall (chart p p) radius ⊆ (chart p).target
  K : NNReal
  K_pos : 0 < K
  anti : AntilipschitzWith K (fderiv ℝ (f ∘ (chart p).symm) (chart p p))
  bound : ∀ y ∈ closedBall (chart p p) radius,
    ‖fderiv ℝ (f ∘ (chart p).symm) y-fderiv ℝ (f ∘ (chart p).symm) (chart p p)‖ < 1/(4*(K:ℝ))

def SurfaceInjectivityPatch.region {f : M → ProjectionTarget 3} {p : M}
    (P : SurfaceInjectivityPatch f p) : Set M :=
  (chart p).source ∩ (chart p) ⁻¹' ball (chart p p) P.radius

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_StandardPreparedCrosscaps
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unconditional generic map has actual standard crosscap charts,
with globally isolated singular values and transverse regular sheets. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

structure SurfaceCrosscapCoordinates (f : M → ProjectionTarget 3) (p : M) where
  source : OpenPartialHomeomorph M Base
  target : OpenPartialHomeomorph (Base × ℝ) (ProjectionTarget 3)
  source_mem : p ∈ source.source
  source_center : source p = 0
  target_mem : 0 ∈ target.source
  target_center : target 0 = f p
  source_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ source source.source
  source_inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ source.symm source.target
  target_smooth : ContDiff ℝ ∞ target
  target_inverse_smooth : ContDiffOn ℝ ∞ target.symm target.target
  model_mem : ∀ x ∈ source.source, standardCrosscap (source x) ∈ target.source
  model_eq : ∀ x ∈ source.source, f x = target (standardCrosscap (source x))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisCurve
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The kernel axis of an actual crosscap chart gives a smooth regular
source curve through the singular point, even though its image velocity vanishes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def crosscapAxis : ℝ →L[ℝ] Base :=
  ContinuousLinearMap.pi ![0,ContinuousLinearMap.id ℝ ℝ]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

def axisCurve (c : SurfaceCrosscapCoordinates f p) : ℝ → M := c.source.symm ∘ crosscapAxis

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ArcTimeChartPartition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite ordered subdivision of the actual embedded arc, in charts
which all use the same global longitudinal coordinate. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

structure SurfaceTimeChart (F : M → ℝ) where
  coord : OpenPartialHomeomorph M Base
  smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ coord coord.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ coord.symm coord.target
  time : ∀ x ∈ coord.source, coord x 1 = F x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseReflection
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing only the transverse coordinate keeps the global arc time
and all axis points unchanged. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def transverseReflection : Base ≃L[ℝ] Base :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x => ![-x 0,x 1]
    invFun := fun x => ![-x 0,x 1]
    left_inv := by intro x; ext i; fin_cases i <;> simp
    right_inv := by intro x; ext i; fin_cases i <;> simp
    map_add' := by intro x y; ext i; fin_cases i <;> simp [add_comm]
    map_smul' := by intro a x; ext i; fin_cases i <;> simp
  }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] {F : M → ℝ}
namespace SurfaceTimeChart

def reflect (c : SurfaceTimeChart F) : SurfaceTimeChart F where
  coord := c.coord.transHomeomorph transverseReflection.toHomeomorph
  smooth := transverseReflection.contDiff.contMDiff.comp_contMDiffOn c.smooth
  inverse_smooth := c.inverse_smooth.comp transverseReflection.symm.contDiff.contMDiff.contMDiffOn
    (fun _ hx => hx)
  time := by
    intro x hx
    change (transverseReflection (c.coord x)) 1 = F x
    exact c.time x hx

end SurfaceTimeChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactDoublePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compactification of the double-pair locus can meet the diagonal
only at singular points. Removing open crosscap neighborhoods leaves a
compact set of genuine distinct double pairs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfaceDoublePairs (f : M → ProjectionTarget 3) : Set (M × M) :=
  {z | z.1 ≠ z.2 ∧ f z.1 = f z.2}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothDoubleAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual double-locus charts retain smooth coordinate expressions in
both directions. Their overlap maps are ordinary smooth real functions. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

structure SmoothDoubleChart (f : M → ProjectionTarget 3) where
  left : M
  right : M
  coord : OpenPartialHomeomorph (surfaceDoublePairs f) ℝ
  expression : Base × Base → ℝ
  expression_smooth : ContDiff ℝ ∞ expression
  source_formula : ∀ z ∈ coord.source,
    z.val.1 ∈ (chart left).source ∧ z.val.2 ∈ (chart right).source ∧
      coord z = expression (chart left z.val.1,chart right z.val.2)
  inverse_left_smooth : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (coord.symm t).val.1) coord.target
  inverse_right_smooth : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (coord.symm t).val.2) coord.target
  inverse_regular : ∀ t ∈ coord.target, Function.Injective
    ((mfderiv 𝓘(ℝ) planeModel (fun s => (coord.symm s).val.1) t).prod
      (mfderiv 𝓘(ℝ) planeModel (fun s => (coord.symm s).val.2) t))

namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

def overlap (a b : SmoothDoubleChart f) : Set ℝ :=
  b.coord.target ∩ b.coord.symm ⁻¹' a.coord.source

def transition (a b : SmoothDoubleChart f) : ℝ → ℝ := a.coord ∘ b.coord.symm

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothDoubleArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact smooth double arc retains the final chart germ. This is
precisely the data needed to continue it through the next chart of a finite cover. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

structure SmoothDoubleArc (f : M → ProjectionTarget 3) where
  arc : SmoothCompactArc (planeModel.prod planeModel) (M × M)
  lift : ℝ → surfaceDoublePairs f
  curve_eq : ∀ t, arc.curve t = (lift t).val
  tail : SmoothDoubleChart f
  sign : ℝ
  sign_eq : sign = 1 ∨ sign = -1
  parameter : ℝ ≃ₜ ℝ
  parameter_smooth : ContDiff ℝ ∞ parameter
  inverse_smooth : ContDiff ℝ ∞ parameter.symm
  parameter_mono : StrictMono parameter
  tail_germ : lift =ᶠ[𝓝 arc.finish] (fun t => tail.coord.symm (sign*parameter t))
  tail_target : sign*parameter arc.finish ∈ tail.coord.target

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularPathCornerChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual common graph charts at every corner of an embedded finite regular path. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

structure RegularPathCornerChart {x y : M} (γ : Path x y) (t : ℝ) where
  chart : OpenPartialHomeomorph M Base
  chart_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ chart chart.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ chart.symm chart.target
  leftGraph : ℝ → ℝ
  rightGraph : ℝ → ℝ
  left_smooth : ContDiff ℝ ∞ leftGraph
  right_smooth : ContDiff ℝ ∞ rightGraph
  leftParameter : ℝ ≃ₜ ℝ
  rightParameter : ℝ ≃ₜ ℝ
  left_parameter_smooth : ContDiff ℝ ∞ leftParameter
  right_parameter_smooth : ContDiff ℝ ∞ rightParameter
  left_inverse_smooth : ContDiff ℝ ∞ leftParameter.symm
  right_inverse_smooth : ContDiff ℝ ∞ rightParameter.symm
  left_monotone : StrictMono leftParameter ∨ StrictAnti leftParameter
  right_monotone : StrictMono rightParameter ∨ StrictAnti rightParameter
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt : lower < t
  lt_upper : t < upper
  upper_lt_one : upper < 1
  left_chart : ∀ u ∈ Icc lower t, γ.extend u ∈ chart.source ∧
    chart (γ.extend u) = ![leftParameter u,leftGraph (leftParameter u)]
  right_chart : ∀ u ∈ Icc t upper, γ.extend u ∈ chart.source ∧
    chart (γ.extend u) = ![rightParameter u,rightGraph (rightParameter u)]
  parameter_match : leftParameter t = rightParameter t

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CornerChartReflection
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing both chart coordinates interchanges the two horizontal
orientations without changing the actual surface branches. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

def reflect (C : RegularPathCornerChart γ t) : RegularPathCornerChart γ t := by
  let e : Base ≃L[ℝ] Base := ContinuousLinearEquiv.neg ℝ
  let q := C.chart.trans e.toHomeomorph.toOpenPartialHomeomorph
  let l := C.leftParameter.trans (Homeomorph.neg ℝ)
  let r := C.rightParameter.trans (Homeomorph.neg ℝ)
  have hql : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ q q.source :=
    e.contDiff.contMDiff.comp_contMDiffOn (C.chart_smooth.mono inter_subset_left)
  have hqr : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ q.symm q.target :=
    C.inverse_smooth.comp e.symm.contDiff.contMDiff.contMDiffOn (fun _ hx => hx.2)
  have hlf : ContDiff ℝ ∞ l := contDiff_neg.comp C.left_parameter_smooth
  have hrf : ContDiff ℝ ∞ r := contDiff_neg.comp C.right_parameter_smooth
  have hli : ContDiff ℝ ∞ l.symm := C.left_inverse_smooth.comp contDiff_neg
  have hri : ContDiff ℝ ∞ r.symm := C.right_inverse_smooth.comp contDiff_neg
  have hlm : StrictMono l ∨ StrictAnti l := by
    rcases C.left_monotone with h | h
    · exact Or.inr (fun _ _ hxy => neg_lt_neg (h hxy))
    · exact Or.inl (fun _ _ hxy => neg_lt_neg (h hxy))
  have hrm : StrictMono r ∨ StrictAnti r := by
    rcases C.right_monotone with h | h
    · exact Or.inr (fun _ _ hxy => neg_lt_neg (h hxy))
    · exact Or.inl (fun _ _ hxy => neg_lt_neg (h hxy))
  refine ⟨q,hql,hqr,(fun x => -C.leftGraph (-x)),(fun x => -C.rightGraph (-x)),
    (C.left_smooth.comp contDiff_neg).neg,(C.right_smooth.comp contDiff_neg).neg,
    l,r,hlf,hrf,hli,hri,hlm,hrm,C.lower,C.upper,C.lower_pos,C.lower_lt,C.lt_upper,C.upper_lt_one,
    ?_,?_,?_⟩
  · intro u hu
    have h := C.left_chart u hu
    refine ⟨⟨h.1,mem_univ _⟩,?_⟩
    change -C.chart (γ.extend u) = ![-C.leftParameter u,-C.leftGraph (- -C.leftParameter u)]
    rw [h.2]
    ext i
    fin_cases i <;> simp
  · intro u hu
    have h := C.right_chart u hu
    refine ⟨⟨h.1,mem_univ _⟩,?_⟩
    change -C.chart (γ.extend u) = ![-C.rightParameter u,-C.rightGraph (- -C.rightParameter u)]
    rw [h.2]
    ext i
    fin_cases i <;> simp
  · change -C.leftParameter t = -C.rightParameter t
    rw [C.parameter_match]

@[simp] lemma reflect_leftParameter_apply (C : RegularPathCornerChart γ t) (u : ℝ) :
    C.reflect.leftParameter u = -C.leftParameter u := rfl

@[simp] lemma reflect_rightParameter_apply (C : RegularPathCornerChart γ t) (u : ℝ) :
    C.reflect.rightParameter u = -C.rightParameter u := rfl

@[simp] lemma reflect_lower (C : RegularPathCornerChart γ t) : C.reflect.lower = C.lower := rfl
@[simp] lemma reflect_upper (C : RegularPathCornerChart γ t) : C.reflect.upper = C.upper := rfl

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_LocalCornerBridge
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual corner of the finite embedded source path admits a
small regular embedded bridge with oriented smooth attachment germs. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} (γ : Path p q) (t : ℝ) (O : Set M)

structure LocalCornerBridge where
  arc : SmoothCompactArc planeModel M
  left : ℝ
  right : ℝ
  left_pos : 0 < left
  left_lt : left < t
  lt_right : t < right
  right_lt_one : right < 1
  leftParameter : ℝ → ℝ
  rightParameter : ℝ → ℝ
  left_smooth : ContDiff ℝ ∞ leftParameter
  right_smooth : ContDiff ℝ ∞ rightParameter
  left_value : leftParameter arc.start = left
  right_value : rightParameter arc.finish = right
  left_forward : 0 < deriv leftParameter arc.start
  right_forward : 0 < deriv rightParameter arc.finish
  left_germ : arc.curve =ᶠ[𝓝 arc.start] γ.extend ∘ leftParameter
  right_germ : arc.curve =ᶠ[𝓝 arc.finish] γ.extend ∘ rightParameter
  image_subset : MapsTo arc.curve (Icc arc.start arc.finish) O

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SeparatedCornerBridge
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local rounding can be chosen disjoint from the entire unchanged
part of the embedded compact source path. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ} {U O : Set M}

namespace LocalCornerBridge

def mono (B : LocalCornerBridge γ t U) (hUO : U ⊆ O) : LocalCornerBridge γ t O where
  arc := B.arc
  left := B.left
  right := B.right
  left_pos := B.left_pos
  left_lt := B.left_lt
  lt_right := B.lt_right
  right_lt_one := B.right_lt_one
  leftParameter := B.leftParameter
  rightParameter := B.rightParameter
  left_smooth := B.left_smooth
  right_smooth := B.right_smooth
  left_value := B.left_value
  right_value := B.right_value
  left_forward := B.left_forward
  right_forward := B.right_forward
  left_germ := B.left_germ
  right_germ := B.right_germ
  image_subset := fun _ hs => hUO (B.image_subset hs)

end LocalCornerBridge

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CornerBridgePath
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turning a separated smooth corner bridge into an embedded replacement
path, retaining finite regular pieces and the exact unchanged trace. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ} {O : Set M}
namespace LocalCornerBridge

def leftPoint (B : LocalCornerBridge γ t O) : I :=
  ⟨B.left,B.left_pos.le,(B.left_lt.trans B.lt_right |>.trans B.right_lt_one).le⟩
def rightPoint (B : LocalCornerBridge γ t O) : I :=
  ⟨B.right,(B.left_pos.trans B.left_lt |>.trans B.lt_right).le,B.right_lt_one.le⟩

end LocalCornerBridge
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapConnectingArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual geometric data for transporting the crosscap-pair replacement.
The arc is embedded and smooth through both endpoint kernel axes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

structure CrosscapConnectingArc (f : M → ProjectionTarget 3) (p q : M) where
  left : SurfaceCrosscapCoordinates f p
  right : SurfaceCrosscapCoordinates f q
  arc : SmoothCompactArc planeModel M
  source : arc.curve arc.start = p
  target : arc.curve arc.finish = q
  regular : ∀ t ∈ Ioo arc.start arc.finish,
    Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (arc.curve t))
  leftParameter : ℝ ≃ₜ ℝ
  rightParameter : ℝ ≃ₜ ℝ
  left_smooth : ContDiff ℝ ∞ leftParameter
  left_inverse_smooth : ContDiff ℝ ∞ leftParameter.symm
  right_smooth : ContDiff ℝ ∞ rightParameter
  right_inverse_smooth : ContDiff ℝ ∞ rightParameter.symm
  left_zero : leftParameter arc.start = 0
  right_zero : rightParameter arc.finish = 0
  left_germ : arc.curve =ᶠ[𝓝 arc.start] left.axisCurve ∘ leftParameter
  right_germ : arc.curve =ᶠ[𝓝 arc.finish] right.axisCurve ∘ rightParameter

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapCoordinateStrip
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual map on a rectangular source strip through two crosscaps,
with a nonzero transverse derivative along the entire central arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {f : M → ProjectionTarget 3} {p q : M}

structure CrosscapCoordinateStrip (A : CrosscapConnectingArc f p q) where
  chart : OpenPartialHomeomorph M Base
  width : ℝ
  width_pos : 0 < width
  chart_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ chart chart.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ chart.symm chart.target
  model : Base → ProjectionTarget 3
  model_smooth : ContDiff ℝ ∞ model
  domain : Set Base
  domain_open : IsOpen domain
  domain_target : domain ⊆ chart.target
  model_eq : EqOn model (f ∘ chart.symm) domain
  axis : ∀ t ∈ Icc A.arc.start A.arc.finish,
    A.arc.curve t ∈ chart.source ∧ chart (A.arc.curve t) = ![0,t]
  rectangle : ∀ x ∈ Icc (-width) width,
    ∀ t ∈ Icc (A.arc.start-width) (A.arc.finish+width), (![x,t] : Base) ∈ domain
  transverse : ∀ t ∈ Icc A.arc.start A.arc.finish,
    fderiv ℝ model (![0,t] : Base) (![1,0] : Base) ≠ 0
  interior_regular : ∀ t ∈ Ioo A.arc.start A.arc.finish,
    Function.Injective (fderiv ℝ model (![0,t] : Base))
  left_vertical : fderiv ℝ model (![0,A.arc.start] : Base) (![0,1] : Base) = 0
  right_vertical : fderiv ℝ model (![0,A.arc.finish] : Base) (![0,1] : Base) = 0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapStripFrame
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth invertible target frame on a neighborhood of the actual strip axis. -/
noncomputable section
open Set Filter Matrix Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

def CrosscapCoordinateStrip.transverseVector (S : CrosscapCoordinateStrip A) (t : ℝ) : Fin 3 → ℝ :=
  EuclideanSpace.equiv (Fin 3) ℝ (fderiv ℝ S.model (crosscapAxis t) (![1,0] : Base))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ShiftedRotationFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation columns with an exterior constant shift. This allows the
twice-winding frame to have two separated simple zeros before filling. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def axisNormalFrame (r y z : ℝ) : Base →L[ℝ] FrameTarget :=
  (ContinuousLinearMap.proj 0).smulRight (![r,0,0] : FrameTarget)+
    (ContinuousLinearMap.proj 1).smulRight (![0,y,z] : FrameTarget)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RelativeDefectFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact frame fillings are preserved by a homotopy whose only zeros stay
inside the fixed compact core. The pasting retains exact exterior values. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def defectFrame (N : Base → Base) (x : Base) : Base →L[ℝ] FrameTarget :=
  axisNormalFrame 1 (N x 0) (N x 1)

/-- The filling changes the frame only on a compact subset of the prescribed
open set; every point of that open set becomes regular. -/
def HasRelativeDefectFilling (N : Base → Base) (U : Set Base) : Prop :=
  ∃ (A : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
    ContDiff ℝ ∞ A ∧ IsCompact K ∧ K ⊆ U ∧
    (∀ x ∈ U, Function.Injective (A x)) ∧
    ∀ x ∉ K, A x = defectFrame N x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SingleTensorRestoreBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed atlas estimate for the single tensor patch of a primitive. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance singleTensorFiberNormed_r34e91d_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance singleTensorFiberSpace_r34e91d_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance singleTensorDualAdd_r34e91d_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance singleTensorDualSmul_r34e91d_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
local instance singleTensorSectionNormed_r34e91d_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance singleTensorSectionSpace_r34e91d_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance singleTensorCentersDecidableEq : DecidableEq A.centers := Classical.decEq _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveFiberInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite rank-one correction acts on symmetric tensors. Adding the
identity on the antisymmetric summand gives an honest invertible operator
on the full four-dimensional tensor fiber, without an orientation choice. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance primitiveInverseFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveInverseFiberSpace_r34e91d_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveInverseFiberComplete_r34e91d_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualSmul
local instance primitiveInverseFiberGroup : AddCommGroup TensorFiber :=
  primitiveInverseFiberNormed.toAddCommGroup

/-- Intrinsic symmetrization of a bilinear form. -/
def tensorSymmetrizer : TensorFiber →L[ℝ] TensorFiber :=
  (1/2 : ℝ) • (ContinuousLinearMap.id ℝ TensorFiber +
    (ContinuousLinearMap.flipₗᵢ ℝ Plane Plane ℝ).toContinuousLinearMap)

variable {ι : Type*} [Fintype ι]

/-- The actual finite supported primitive operator, in one fiber. -/
def finitePrimitiveOperator (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) : TensorFiber →L[ℝ] TensorFiber :=
  ∑ i, (psi i)^2 • ((q i).comp tensorSymmetrizer).smulRight ((xi i).smulRight (xi i))

def completedPrimitiveOperator (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) : TensorFiber →L[ℝ] TensorFiber :=
  finitePrimitiveOperator q psi xi + ContinuousLinearMap.id ℝ TensorFiber - tensorSymmetrizer

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPrimitiveOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fiberwise correction operator for independently perturbed
primitive cutoffs. Its reference value is the identity, and its inverse
solves the finite rank-one equation on the original tensor bundle. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

local instance atlasOperatorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasOperatorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasOperatorFiberComplete_r34e91d_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance atlasOperatorDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasOperatorDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasOperatorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)

namespace SmoothingAtlas
local instance atlasOperatorFiberComplete_r34e91d_2 : CompleteSpace TensorFiber := inferInstance
variable (A : SmoothingAtlas M)

local instance atlasOperatorSectionSpace_r34e91d_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance atlasOperatorSectionGroup_r34e91d_1 (p : M) : AddCommGroup (CovariantTwoTensor p) :=
  (atlasOperatorSectionNormed p).toAddCommGroup
def primitivePhaseCovector (phi : (A.centers × Fin 3) → M → ℝ)
    (a : A.centers × Fin 3) (p : M) : Plane →L[ℝ] ℝ :=
  mfderiv planeModel 𝓘(ℝ) (phi a) p

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorOperatorFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tensor operators and their inverses in a fixed primitive frame. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance operatorFrameFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance operatorFrameFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance operatorFrameDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace SmoothingAtlas
local instance operatorFrameDualSmul_r34e91d_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

local instance operatorFrameSectionNormed_r34e91d_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance operatorFrameSectionSpace_r34e91d_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorOperatorFrame (i : B.centers) (p : M)
    (T : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) : TensorFiber →L[ℝ] TensorFiber :=
  ((B.tensorTriv i).continuousLinearMapAt ℝ p).comp (T.comp ((B.tensorTriv i).symmL ℝ p))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorFrameAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate conjugation of the actual primitive operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance frameAlgebraFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance frameAlgebraFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance frameAlgebraDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace SmoothingAtlas
local instance frameAlgebraDualSmul_r34e91d_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

local instance frameAlgebraSectionNormed_r34e91d_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameAlgebraSectionSpace_r34e91d_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def covectorFrame (i : B.centers) (p : M) (v : Plane →L[ℝ] ℝ) : Plane →L[ℝ] ℝ :=
  v.comp ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth orthonormal frames obtained by interpolating non-antipodal plane directions. -/
noncomputable section
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma dot_self_pos {v : Vec} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have hn : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  exact hn.lt_of_ne' ((dotProduct_self_eq_zero).not.mpr hv)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityCircleLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lift a normalized planar loop to the actual four-dimensional velocity
plane, retaining its exact mean, length, and leading metric. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

/-- The fixed orthonormal-plane inclusion, written as a continuous linear map. -/
def planeLift (e₁ e₂ : Vec) : LoopDensity.Plane →L[ℝ] Vec :=
  (ContinuousLinearMap.proj 0).smulRight e₁ + (ContinuousLinearMap.proj 1).smulRight e₂

@[simp] lemma planeLift_apply (e₁ e₂ : Vec) (p : LoopDensity.Plane) :
    planeLift e₁ e₂ p = p 0 • e₁ + p 1 • e₂ := rfl

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityCoordinateData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth velocity coordinates and their calibrated collar values. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dot_smoothOn {f g : E → Vec} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun x => f x ⬝ᵥ g x) U :=
  ContDiffOn.sum (fun i _ => (contDiffOn_pi.mp hf i).mul (contDiffOn_pi.mp hg i))

def velocityRadius (v : Vec) (a : ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v + a ^ 2)

lemma velocityRadius_pos {v : Vec} {a : ℝ} (h : v ≠ 0 ∨ a ≠ 0) :
    0 < velocityRadius v a := by
  apply Real.sqrt_pos.mpr
  rcases h with hv | ha
  · exact add_pos_of_pos_of_nonneg (dot_self_pos hv) (sq_nonneg a)
  · exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (sq_pos_of_ne_zero ha)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal frames and scaled second-form coefficients are smooth functions of
exactly the five derivative components retained by the primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

abbrev BoundaryProfile := Fin 5 → Vec

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicFamilies
attribute [-simp] _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.zero_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic families used in the finite metric expansion. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector SmoothPeriodicCalculus

variable (A E : Type) [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def smoothFamilies : Submodule ℝ (A → C(Period, E)) where
  carrier := {F | ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))}
  zero_mem' := by change ContDiff ℝ ∞ (fun _ : A × ℝ => (0 : E)); exact contDiff_const
  add_mem' := by
    intro F G hF hG
    change ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)) at hF
    change ContDiff ℝ ∞ (fun z : A × ℝ => G z.1 (z.2 : Period)) at hG
    change ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period) + G z.1 (z.2 : Period))
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    change ContDiff ℝ ∞ (fun z : A × ℝ => c • F z.1 (z.2 : Period))
    exact contDiff_const.smul hF

def Family := ↥(smoothFamilies A E)

instance instAddCommGroupFamily : AddCommGroup (Family A E) :=
  inferInstanceAs (AddCommGroup ↥(smoothFamilies A E))
instance instModuleRealFamily : Module ℝ (Family A E) :=
  inferInstanceAs (Module ℝ ↥(smoothFamilies A E))

variable {A E}

namespace Family

def val (F : Family A E) : A → C(Period, E) := F.1

lemma smooth (F : Family A E) :
    ContDiff ℝ ∞ (fun z : A × ℝ => F.val z.1 (z.2 : Period)) := F.2

@[ext] lemma ext {F G : Family A E} (h : ∀ p t, F.val p t = G.val p t) : F = G := by
  apply Subtype.ext
  funext p
  exact ContinuousMap.ext (h p)

@[simp] lemma zero_apply (p : A) (t : Period) : (0 : Family A E).val p t = 0 := rfl
@[simp] lemma add_apply (F G : Family A E) (p : A) (t : Period) :
    (F + G).val p t = F.val p t + G.val p t := rfl
@[simp] lemma neg_apply (F : Family A E) (p : A) (t : Period) :
    (-F).val p t = -F.val p t := rfl
@[simp] lemma sub_apply (F G : Family A E) (p : A) (t : Period) :
    (F - G).val p t = F.val p t - G.val p t := rfl
@[simp] lemma smul_apply (c : ℝ) (F : Family A E) (p : A) (t : Period) :
    (c • F).val p t = c • F.val p t := rfl

@[simp] lemma sum_apply {ι : Type*} (s : Finset ι) (F : ι → Family A E)
    (p : A) (t : Period) : (∑ i ∈ s, F i).val p t = ∑ i ∈ s, (F i).val p t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

def slow (F : Family A E) (v : A) : Family A E :=
  ⟨slowDerivativeFamily F.val F.smooth v, slowDerivativeFamily_smooth F.val F.smooth v⟩

def angle (F : Family A E) : Family A E :=
  ⟨derivativeFamily F.val F.smooth, derivativeFamily_smooth F.val F.smooth⟩

@[simp] lemma slow_apply (F : Family A E) (v p : A) (t : ℝ) :
    (F.slow v).val p (t : Period) =
      slowDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) v (p, t) := rfl

@[simp] lemma angle_apply (F : Family A E) (p : A) (t : ℝ) :
    F.angle.val p (t : Period) =
      angleDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) := rfl

variable [FiniteDimensional ℝ A] [CompleteSpace E]

def inner (F G : Family A E) : Family A ℝ :=
  ⟨fun p => ⟨fun t => Inner.inner ℝ (F.val p t) (G.val p t),
    (F.val p).continuous.inner (G.val p).continuous⟩, F.smooth.inner ℝ G.smooth⟩

omit [FiniteDimensional ℝ A] [CompleteSpace E] in
@[simp] lemma inner_apply (F G : Family A E) (p : A) (t : Period) :
    (F.inner G).val p t = Inner.inner ℝ (F.val p t) (G.val p t) := rfl

end Family

namespace Family

def constant (f : A → E) (hf : ContDiff ℝ ∞ f) : Family A E :=
  ⟨fun p => ContinuousMap.const Period (f p), hf.comp contDiff_fst⟩

@[simp] lemma constant_apply (f : A → E) (hf : ContDiff ℝ ∞ f) (p : A) (t : Period) :
    (constant f hf).val p t = f p := rfl

variable [FiniteDimensional ℝ A]

def mean (F : Family A ℝ) : Family A ℝ :=
  constant (fun p => average (F.val p)) (contDiff_average_joint F.smooth)

def fluct (F : Family A ℝ) : Family A ℝ := F - F.mean

@[simp] lemma mean_apply (F : Family A ℝ) (p : A) (t : Period) :
    F.mean.val p t = average (F.val p) := rfl

@[simp] lemma fluct_apply (F : Family A ℝ) (p : A) (t : Period) :
    F.fluct.val p t = fluctuation (F.val p) t := rfl

end Family
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five Euclidean profiles used by the exact primitive determine the
canonical normal frame in the real surface coordinates. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open RealModes NormalFrame JetVelocityCoordinates

abbrev EuclideanBoundaryProfile := Fin 5 → Euclidean

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOperatorStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform stability of the finite primitive inverse when its coefficient
functionals, cutoffs and phase covectors all vary independently. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance dataFiberNormed_r34e91d_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance dataFiberSpace_r34e91d_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance dataFiberComplete_r34e91d_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataDualAdd
local instance dataDualSmul_r34e91d_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

abbrev PrimitiveOperatorData (ι : Type*) :=
  ((ι → TensorFiber →L[ℝ] ℝ) × (ι → ℝ)) × (ι → Plane →L[ℝ] ℝ)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveAmplitudeParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact C1 control of the actual inverse and square-root amplitude map.
The parameter bounds are fixed before a later family is composed with it. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance amplitudeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance amplitudeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance amplitudeFiberComplete_r34e91d_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeDualAdd
local instance amplitudeDualSmul_r34e91d_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance amplitudeFiberGroup : AddCommGroup TensorFiber := amplitudeFiberNormed.toAddCommGroup
variable {ι : Type*} [Fintype ι]

abbrev PrimitiveAmplitudeData (ι : Type*) := PrimitiveOperatorData ι × TensorFiber

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveAmplitudeChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary chain-rule estimate used for each actual amplitude chart. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance ampChainFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance ampChainFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance ampChainTensorDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance ampChainTensorDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainPlaneDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainPlaneDualSpace
local instance ampChainFiberT2_r34e91d_1 : T2Space TensorFiber := inferInstance
local instance ampChainTensorDualT2_r34e91d_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance ampChainPlaneDualT2_r34e91d_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]
local instance ampChainDataNormed : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance ampChainDataSpace : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteCrosscapCleanup
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prepared finite-crosscap map with global self-transversality and no
additional preimage of any singular point image, preserving every quadratic germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

def QuadraticCrosscapGerms (f : M → ProjectionTarget 3) : Prop :=
  ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
    ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
      p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
      f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
      surfaceDirection φ b (chart q p,t) = 0 ∧
      Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end


