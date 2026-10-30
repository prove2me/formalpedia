-- Prove2me | Definitions.Def_OAIQ088F001
-- name    : OAIQ088F001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:38:35.746492+00:00
-- url     : https://prove2.me/theorems/e90a04da-19b6-485d-855a-7ca1e2a7b4ff
-- title:
--   Definitions bundle OAIQ088F001 of the split of OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 243 declarations of OpenAI's Lean: 146 definitions, 8 inductive types or structures, 8 instances and 81 theorems. The definitions and types are `OAI.Falconer.ProfileCellFamily`, `OAI.Falconer.PublishedFiniteLoomisWhitney`, `OAI.Falconer.Regularization.finiteRampProfile`, `OAI.Falconer.Regularization.intervalRamp`, `OAI.Falconer.Regularization.leafBinEndpoint`, `OAI.Falconer.Regularization.leafMassBin`, `OAI.Falconer.Regularization.massBinCandidates`, `OAI.Falconer.Regularization.parallelPackingConstant`, `OAI.Falconer.Regularization.scalarCompressedBranch`, `OAI.Falconer.Regularization.scalarEffectiveLevel`, `OAI.Falconer.Regularization.scalarNonporousLevels`, `OAI.Falconer.Regularization.scalarPorousLevels`, `OAI.Falconer.Regularization.scalarSelectedScale`, `OAI.Falconer.RobustProfileContact`, `OAI.Falconer.ScalarBinaryTail`, `OAI.Falconer.ScalarBunch`, `OAI.Falconer.ScalarBunchChain`, `OAI.Falconer.ScalarBunchGood`, `OAI.Falconer.ScalarClusterTree`, `OAI.Falconer.SmoothSeparation`, `OAI.Falconer.SmoothSeparation.scaleTerms`, `OAI.Falconer.SmoothSeparation.value`, `OAI.Falconer.StructuredProfilePieces`, `OAI.Falconer.WeakRadialLosses`, `OAI.Falconer.cellContraction`, `OAI.Falconer.chartDensityKernel`, `OAI.Falconer.chartLineKernel`, `OAI.Falconer.clipProfilePrefix`, `OAI.Falconer.coarseSlabConstant`, `OAI.Falconer.commonTripleRelation`, `OAI.Falconer.commonTupleRelation`, `OAI.Falconer.densityFailure`, `OAI.Falconer.determinantTerms`, `OAI.Falconer.directionalLaplacian`, `OAI.Falconer.directionalLaplacianTrace`, `OAI.Falconer.distanceWeight`, `OAI.Falconer.dropGridCoordinate`, `OAI.Falconer.dyadicAverage`, `OAI.Falconer.dyadicCells`, `OAI.Falconer.dyadicEndpoints` and 114 more.
--
--   **Sources.** They come from these modules of lean/OAI/MeasureTheory, in whole or in part: `Falconer_Angular_AngularChart`, `Falconer_Angular_AngularGainFinite`, `Falconer_Angular_GoodProjectionDirections`, `Falconer_Estimates_ActualOuterMasks`, `Falconer_Estimates_AllDimensions`, `Falconer_Estimates_CellClassifier`, `Falconer_Estimates_DyadicAveraging`, `Falconer_Estimates_DyadicCells`, `Falconer_Estimates_DyadicSecantError`, `Falconer_Estimates_DyadicSlopeEnergy`, `Falconer_Estimates_DyadicSlopeVariance`, `Falconer_Estimates_FinitePartitionMask`, `Falconer_Estimates_FinitePopularity`, `Falconer_Estimates_GeneralTransverseCount`, `Falconer_Estimates_IidSampling`, `Falconer_Estimates_LaplacianBounds`, `Falconer_Estimates_LinearPieces`, `Falconer_Estimates_MonotoneLowpass`, `Falconer_Estimates_NearPinDeletion`, `Falconer_Estimates_OriginalWeakCosts`, `Falconer_Estimates_OuterRootGain`, `Falconer_Estimates_PlanarSampling`, `Falconer_Estimates_PrunedVariation`, `Falconer_Estimates_Published`, `Falconer_Estimates_QuadraticDifferential`, `Falconer_Estimates_RestorationSeries`, `Falconer_Estimates_ScalarBinaryParameters`, `Falconer_Estimates_ScalarBunchSizes`, `Falconer_Estimates_ScalarBunchTransfer`, `Falconer_Estimates_ScalarBunchTree`, `Falconer_Estimates_ScalarBunchingSuffix`, `Falconer_Estimates_ScalarClusterTree`, `Falconer_Estimates_ScalarCoefficientBudget`, `Falconer_Estimates_ScalarCoefficientClosure`, `Falconer_Estimates_ScalarCompressedLevels`, `Falconer_Estimates_ScalarCorrelatedWeights`, `Falconer_Estimates_ScalarInitialGrowth`, `Falconer_Estimates_ScalarLevelEnumeration`, `Falconer_Estimates_ScalarLogAverages`, `Falconer_Estimates_ScalarNonporousPowers`, `Falconer_Estimates_ScalarPartialSums`, `Falconer_Estimates_ScalarPorousLevels`, `Falconer_Estimates_ScalarSumCells`, `Falconer_Estimates_ScalarSwitchSums`, `Falconer_Estimates_ScalarZoom`, `Falconer_Estimates_TripleGram`, `Falconer_Estimates_TripleGramStability`, `Falconer_Fourier_ChartDerivatives`, `Falconer_Fourier_FourStationaryPhases`, `Falconer_Fourier_LocalStationaryJets`, `Falconer_Fourier_MaskJetSeparation`, `Falconer_Fourier_PhaseIntegration`, `Falconer_Fourier_SeparatedJets`, `Falconer_Geometry_GeneralGridRounding`, `Falconer_Geometry_OneScaleGeometry`, `Falconer_Geometry_PlanarScalarGrid`, `Falconer_Geometry_ProjectionRatioGeometry`, `Falconer_Geometry_ProjectionSampleBudget`, `Falconer_Geometry_RobustProjectionSets`, `Falconer_Geometry_SamplingGrid`, `Falconer_Geometry_ScalarBallCandidates`, `Falconer_Geometry_ScalarGridFibers`, `Falconer_Geometry_ScalarNormalizationCost`, `Falconer_Geometry_ScalarNormalizedLogBudget`, `Falconer_Geometry_ScalarNormalizedProjection`, `Falconer_Geometry_TripleGridRounding`, `Falconer_Graphs_BipartitePivot`, `Falconer_Graphs_RegularGraphCosts`, `Falconer_Incidence_BlockCellNormalGain`, `Falconer_Incidence_CommonTripleIncidence`, `Falconer_Incidence_CommonTupleIncidence`, `Falconer_Incidence_FiniteBallPruning`, `Falconer_Incidence_LeafMassBins`, `Falconer_Incidence_PublishedLoomisWhitney`, `Falconer_Incidence_RadialBlockDepths`, `Falconer_Measures_DensityTruncation`, `Falconer_Measures_FiberDensityPruning`, `Falconer_Measures_FirstExclusionMass`, `Falconer_Measures_FrequencyMeasure`, `Falconer_Measures_MeanProbability`, `Falconer_Measures_MultiscaleDensityPruning`, `Falconer_Radial_CoarsePlateAffineBound`, `Falconer_Radial_PlateScales`, `Falconer_Radial_ScalarAffineExceptions`, `Falconer_Radial_SignedRadialKernel`, `Falconer_Radial_WeakRadialLosses`, `Falconer_Recursion_FiniteCountingPotential`, `Falconer_Recursion_FiniteCriticalPotential`, `Falconer_Recursion_InnerProfileGrid`, `Falconer_Recursion_ParallelProfile`, `Falconer_Recursion_PlanarCriticalPotential`, `Falconer_Recursion_PointRieszPotential`, `Falconer_Recursion_ProfileCellFamily`, `Falconer_Recursion_ProfileGainAccounting`, `Falconer_Recursion_ProfileGridCells`, `Falconer_Recursion_ProfileHighMass`, `Falconer_Recursion_ProfileInterpolation`, `Falconer_Recursion_ProfileIntervalChain`, `Falconer_Recursion_ProfilePrefix`, `Falconer_Recursion_ProfileStepBudget`, `Falconer_Recursion_ProfileSuffixMinimum`, `Falconer_Recursion_ScalarBinaryBranch`, `Falconer_Recursion_ScalarBunchingLedger`, `Falconer_Recursion_ThreeIntervalData`, `Falconer_Recursion_UniformProfileContact`, `Falconer_Shells_HalfDimensionalShell`, `Falconer_Shells_MonotoneShellCriterion`, `Falconer_Slicing_DyadicSliceSelection`, `Falconer_Slicing_GaussianBand`, `Falconer_Slicing_GaussianLebesgue`, `Falconer_Slicing_GaussianLocalBand`, `Falconer_Slicing_GaussianMass`, `Falconer_Slicing_GaussianMomentWeights`, `Falconer_Slicing_GaussianPairBand`, `Falconer_Slicing_GaussianThreshold`, `Falconer_Slicing_GaussianTruncatedTriple`, `Falconer_Slicing_GaussianVectorBand`, `Falconer_Slicing_SliceNormalization`.
--
--   **Imports.** It imports the published bundle `Def_PlanarFalconer`; the bundle `OAIQ038F002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ088F002` and `OAIQ088F003`; the statements `OAI.Falconer.Regularization.endpoint_one_scale_gain`, `OAI_Falconer_Regularization_endpoint_two_sided_one_scale`, `OAI_Falconer_Regularization_scalar_bounded_projection`, `OAI.Falconer.Regularization.scalar_dyadic_projection`, `OAI.Falconer.centered_packet_product_power`, `OAI_Falconer_endpoint_dyadic_angular_gain`, `OAI_Falconer_eventually_initial_plate_loss`, `OAI_Falconer_planar_case_of_published_radial`, `OAI_Falconer_scalar_normalized_projection_bound`, `OAI.Falconer.small_chart_weak_radial` and `OAI_PlanarFalconer_exists_normalized_root_setup_of_published_radial`; the proofs of `OAI_Falconer_planar_case_of_published_radial`, `OAI_Falconer_scalar_normalized_projection_bound` and `OAI_PlanarFalconer_exists_normalized_root_setup_of_published_radial`.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MeasureTheory at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section
-- module Solutions.OAIQ088_FD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The all-dimensional Falconer statement and the final measure argument

The Falconer distance conjecture concerns compact subsets of Euclidean
space with Hausdorff dimension greater than half the ambient dimension.
The dimension-independent final measure argument reduces positivity of
the original distance set to absolute continuity of a weighted distance
pushforward.
-/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

section Measures
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- The weight in the classical threshold argument, and in the spherical
stationary-phase normalization, is `dist ^ (-(d-1)/2)`. -/
noncomputable def distanceWeight (a : ℝ) (z : X × X) : ℝ≥0∞ :=
  ENNReal.ofReal ((dist z.1 z.2) ^ (-a))

end Measures
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A normalized affine line in a spherical chart

Differentiation in a gnomonic chart is the tangential projection of the
coordinate direction divided by the normalization. This connects the
failed perpendicular test to an ordinary one-variable phase derivative.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normalizedLine (a t : E) (u : ℝ) : E :=
  ‖a + u • t‖⁻¹ • (a + u • t)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularGainFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite labelled incidence obstruction

The sampling argument in `ang:planar-measures` ends with finite point
and line families. Their counting contradiction follows
from the precise published Furstenberg input. All line families must use
a common separated grid before cardinalities replace covering numbers.
Direction labels remain distinct throughout the upper counting estimate.
-/

namespace Falconer
open Set
open scoped BigOperators

/-- Rounding a line coordinate to a grid of mesh `δ`. -/
noncomputable def lineGridRound (δ a : ℝ) : ℝ := δ * (round (a / δ) : ℝ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSumCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer-cell comparison for scalar sumsets. These constant-factor
bridges allow the finite additive-combinatorial estimates to be applied
at the same scale as the parameter projections. -/
namespace Falconer
open scoped Pointwise

noncomputable def scalarCells (δ : ℝ) (A : Finset ℝ) : Finset ℤ :=
  A.image fun x => ⌊x/δ⌋

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FinitePopularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative popular-parameter selection in the finite incidence
argument. No asymptotic notation or hidden logarithmic losses are used. -/
namespace Falconer

noncomputable def familyDegree {α β : Type*} [DecidableEq β] (J : Finset α) (A : α → Finset β) (x : β) : ℝ :=
  ((J.filter fun j => x ∈ A j).card : ℝ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_BipartitePivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dense-neighborhood pivot used in the scalar additive-energy
argument. Integer vertices are sufficient for the quantized sumsets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def integerNeighbors (B : Finset ℤ) (e : ℤ → ℤ → Prop) (a : ℤ) : Finset ℤ :=
  B.filter fun b => e a b

noncomputable def integerCommonNeighbors (A : Finset ℤ) (e : ℤ → ℤ → Prop)
    (b c : ℤ) : Finset ℤ := A.filter fun a => e a b ∧ e a c

noncomputable def integerBadPairs (A B : Finset ℤ) (e : ℤ → ℤ → Prop) (L : ℝ) :
    Finset (ℤ × ℤ) := (B ×ˢ B).filter fun p => ((integerCommonNeighbors A e p.1 p.2).card : ℝ) < L

noncomputable def integerBadPairsAt (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    (L : ℝ) (a : ℤ) : Finset (ℤ × ℤ) :=
  (integerBadPairs A B e L).filter fun p => e a p.1 ∧ e a p.2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarBallCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite critical radii for maximizing scalar local density. -/
namespace Falconer

noncomputable def scalarBallCandidates (δ : ℝ) (E : Finset ℝ) : Finset (ℝ × ℝ) :=
  (E ×ˢ E).image (fun p => (p.1,max δ |p.2-p.1|)) ∪ E.image (fun x => (x,2))

noncomputable def scalarBallMass (E : Finset ℝ) (u r : ℝ) : ℝ :=
  ((E.filter fun x => |x-u| ≤ r).card : ℝ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarZoom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite scalar zooming and its ball-count identity. -/
namespace Falconer

noncomputable def scalarZoom (z R : ℝ) (E : Finset ℝ) : Finset ℝ :=
  E.image fun x => (x-z)/R

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ScalarAffineExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional coefficient counts for separated scalar clusters. This is
 the finite real-variable separation estimate in the porous amplification
 argument; the coefficient distribution is the original finite set. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def scalarBadClusterCoefficients (B X Y : Finset ℝ) (R : ℝ) : Finset ℝ :=
  B.filter fun b => ∃ p ∈ X ×ˢ Y, ∃ q ∈ X ×ˢ Y,
    p ≠ q ∧ |(p.1+b*p.2)-(q.1+b*q.2)| ≤ R

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FiniteCountingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite point potential needed by the elementary planar incidence bound. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def planarPotentialConstant (b f : ℝ) : ℝ :=
  1+(2:ℝ)^b*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FiniteCriticalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The critical dyadic potential of a finite scalar statistic, with one
explicit contribution per scale. This is used for the average projected
energy of a planar point set. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def scalarCountingMeasure (I : Finset ℝ) : Measure ℝ :=
  ∑ c ∈ I, Measure.dirac c

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GoodProjectionDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At least half of the original direction labels have bounded projected
energy. No direction is replaced and the estimate is uniform over later
subsets of the planar point set. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def projectionEnergyBudget (N : ℕ) (s t KI KP : ℝ) : ℝ :=
  1+((2:ℝ)^s*(1+(N:ℝ)*(2:ℝ)^s)*KI*(8:ℝ)^s)*KP*planarPotentialConstant s t

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ActualOuterMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem sourcePolicyBlock_pos {N : ℕ} (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) :
    0 < sourcePolicyBlock N kap := by
  unfold sourcePolicyBlock
  exact Nat.ceil_pos.mpr (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform derivatives of the normalized line chart

The scalar denominator is a smooth function of two real variables on a
fixed compact square. Its bounds are independent of the chart center,
tangent direction, and displacement. No analytic input is assumed here.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def partialSecond (F : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => F
  | n+1 => fun p => fderiv ℝ (partialSecond F n) p (0,1)

noncomputable def chartLineKernel (p : ℝ × ℝ) : ℝ :=
  (Real.sqrt (1+p.1^2+p.2^2))⁻¹

noncomputable def chartDensityKernel (d : ℕ) (p : ℝ × ℝ) : ℝ :=
  (1+p.1^2+p.2^2)^(-(d : ℝ)/2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PhaseIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinate integration by parts for the angular localization

For an arbitrary smooth real phase in a sphere chart, coordinate integration
by parts gives a scale bound through the reciprocal phase derivative.
The transport derivative identities concern functions on the real line and
are independent of the ambient sphere dimension.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

noncomputable def phaseOscillator (φ : ℝ → ℝ) (Λ x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (Λ : ℂ) * (φ x : ℂ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LeafMassBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original leaf mass bins with the dimension-dependent cutoff -/

namespace Falconer.Regularization
open MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def massBinCandidates (d N : ℕ) (w : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range ((d+2)*N+1)).filter fun k => (2:ℝ)^k ≤ (2:ℝ)^((d+2)*N)*w

noncomputable def leafMassBin (d N : ℕ) (w : ℝ) : ℕ :=
  if h : (massBinCandidates d N w).Nonempty then (massBinCandidates d N w).max' h else 0

noncomputable def leafBinEndpoint (d N k : ℕ) : ℝ := (2:ℝ)^k / (2:ℝ)^((d+2)*N)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Profiles with the correct all-dimensional slope

The logarithmic child counts are linearly interpolated. Their exact slope
bound is d/N; after rescaling the depth interval to [0,1] it is d.
-/

namespace Falconer.Regularization
variable {d : ℕ}

noncomputable def intervalRamp (a b u : ℝ) : ℝ := min u b - min u a

noncomputable def finiteRampProfile (d c : ℕ → ℝ) (K : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, c i * intervalRamp (d (i+1)) (d i) u

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FrequencyMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball bounds for an actual radial frequency-shell pushforward -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

def radialFrequencyAnnulus (B : ℝ) : Set ℝ := {t | B ≤ |t| ∧ |t| ≤ 2*B}

def radialWindow (a r : ℝ) : Set ℝ := Ioo (a-r) (a+r) ∪ Ioo (-a-r) (-a+r)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian mass at a finite Frostman scale

Only ball bounds at radii at least `B⁻¹` are used. This is the spatial
Gaussian estimate in the proof of the half-dimensional Fourier estimate.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable def gaussianBallConstant (k : ℕ) : ℝ :=
  ∑' n : ℕ, Real.exp (-(n:ℝ))*((n:ℝ)+1)^k

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def gaussianMassTerm (x : X) (B : ℝ) (n : ℕ) : X → ℝ≥0∞ :=
  (ball x (((n:ℝ)+1)/B)).indicator (fun _ => ENNReal.ofReal (Real.exp (-(n:ℝ))))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_HalfDimensionalShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The critical half-dimensional estimate on one frequency shell -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def halfDimensionalShellConstant (d : ℕ) : ℝ :=
  ((Real.pi/2)^((d:ℝ)/2))⁻¹ *
    (Real.exp 1*8*(2:ℝ)^((d:ℝ)/2)*gaussianBallConstant (Nat.ceil ((d:ℝ)/2+1))) *
    (16*Real.pi)^((d:ℝ)/2)*gaussianBallConstant (Nat.ceil ((d:ℝ)/2))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ParallelProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The inverse-power sum for actual parallel-test centers

The critical kernel exponent is arbitrary here so the application can
use d/2. Every counted center belongs to the original normalized class.
-/

namespace Falconer.Regularization
open Set Metric MeasureTheory
variable {d : ℕ}

noncomputable def parallelPackingConstant (d : ℕ) : ℕ :=
  max ((2*Nat.ceil (20*((d:ℝ)+1)+2*Real.sqrt d)+1)^d)
    ((2*Nat.ceil (2+2*Real.sqrt d)+1)^d)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LaplacianBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative finite-derivative bounds for stationary jets

The Laplacian is a fixed finite sum of second directional derivatives.
Expressing that contraction as a continuous linear map gives bounds for
all mixed Fréchet derivatives, without replacing them by separate bounds
on a single chart coordinate. Vertical unit vectors in a parameter/tangent
product give the partial Laplacian used by the actual stationary operators.
-/

namespace Falconer
open scoped BigOperators ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable local instance instNormedSpaceRealContinuousLinearMapIdComplex_solutions : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance
noncomputable local instance instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance

noncomputable def directionalLaplacianTrace {n : ℕ} (v : Fin n → E) :
    (E →L[ℝ] E →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ∑ i : Fin n, (ContinuousLinearMap.apply ℝ ℂ (v i)).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℂ) (v i))

@[simp] theorem directionalLaplacianTrace_apply {n : ℕ} (v : Fin n → E)
    (T : E →L[ℝ] E →L[ℝ] ℂ) : directionalLaplacianTrace v T = ∑ i : Fin n, T (v i) (v i) := by
  simp [directionalLaplacianTrace]

noncomputable def directionalLaplacian {n : ℕ} (v : Fin n → E) (f : E → ℂ) : E → ℂ :=
  fun x => directionalLaplacianTrace v (fderiv ℝ (fderiv ℝ f) x)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CellClassifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable Borel labels for the actual endpoint masks

Every descriptor anchored above a fixed depth is constant on that depth's
cells. The label also records points outside the original cube.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

instance cellLabelMeasurableSpace (d : ℕ) : MeasurableSpace (Option (List (Fin d → Bool))) := ⊤

instance cellLabelMeasurableSingletonClass (d : ℕ) :
    MeasurableSingletonClass (Option (List (Fin d → Bool))) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicSlopeEnergy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic slope energies for the quantitative differentiation of the
planar branching profile. Only the Lipschitz constant two is needed. -/
namespace Falconer

noncomputable def intervalSecantSlope (f : ℝ → ℝ) (a h : ℝ) : ℝ :=
  (f (a+h)-f a)/h

noncomputable def dyadicSlopeEnergy (f : ℝ → ℝ) (a h : ℝ) : ℕ → ℝ
  | 0 => (intervalSecantSlope f a h)^2
  | n+1 => (dyadicSlopeEnergy f a (h/2) n + dyadicSlopeEnergy f (a+h/2) (h/2) n)/2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicSlopeVariance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact variance and selection of a small energy increment for dyadic slopes. -/
namespace Falconer
open scoped BigOperators

noncomputable def dyadicSlopeVariance (f : ℝ → ℝ) (a h c : ℝ) : ℕ → ℝ
  | 0 => (intervalSecantSlope f a h-c)^2
  | n+1 => (dyadicSlopeVariance f a (h/2) c n + dyadicSlopeVariance f (a+h/2) (h/2) c n)/2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicAveraging
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dyadic averaging and the energy increment identity. -/
namespace Falconer

noncomputable def dyadicAverage (g : ℝ → ℝ → ℝ) (a h : ℝ) : ℕ → ℝ
  | 0 => g a h
  | n+1 => (dyadicAverage g a (h/2) n+dyadicAverage g (a+h/2) (h/2) n)/2

@[simp] theorem dyadicAverage_const (c a h : ℝ) (n : ℕ) :
    dyadicAverage (fun _ _ => c) a h n = c := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicAverage,ih]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit ordered dyadic interval partition and its weighted averages. -/
namespace Falconer
open Set

noncomputable def dyadicCells (a h : ℝ) : ℕ → List (ℝ × ℝ)
  | 0 => [(a,h)]
  | n+1 => dyadicCells a (h/2) n ++ dyadicCells (a+h/2) (h/2) n

@[simp] theorem dyadicCells_length (a h : ℝ) (n : ℕ) :
    (dyadicCells a h n).length = 2^n := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicCells,List.length_append,ih,pow_succ]; omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicSecantError
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise straight-line error on the dyadic vertices is controlled by
the centered slope energy, without any differentiability assumption. -/
namespace Falconer
open Set

noncomputable def intervalSecantError (f : ℝ → ℝ) (a h x : ℝ) : ℝ :=
  f x-f a-intervalSecantSlope f a h*(x-a)

def dyadicEndpoints (a h : ℝ) : ℕ → Set ℝ
  | 0 => {a,a+h}
  | n+1 => dyadicEndpoints a (h/2) n ∪ dyadicEndpoints (a+h/2) (h/2) n

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrunedVariation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact variation cost of deleting original pairs

The full filtered measure is monotone in the coarse filter. Its pruned
approximation differs by precisely the weighted mass of the removed pairs.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem finite_withDensity_of_bounded (π : Measure X) [IsFiniteMeasure π]
    (w : X → ℝ≥0∞) {C : ℝ≥0∞} (hC : C < ∞) (hbound : ∀ᵐ x ∂π, w x ≤ C) :
    IsFiniteMeasure (π.withDensity w) := by
  constructor
  rw [withDensity_apply w MeasurableSet.univ,Measure.restrict_univ]
  apply lt_of_le_of_lt (lintegral_mono_ae hbound)
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hC (measure_lt_top π univ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FinitePartitionMask
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded measurable masks on a finite disjoint spatial partition -/

namespace Falconer
open Set MeasureTheory
variable {X ι : Type*} [MeasurableSpace X]

noncomputable def finitePartitionMask (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ) : X → ℝ :=
  fun x => ∑ i ∈ F, (C i).indicator (w i) x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TripleGram
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram determinants for the endpoint's three original chart directions -/

namespace Falconer
variable {n : ℕ}

noncomputable def tripleGram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : ℝ := (Matrix.gram ℝ ![a,b,c]).det

def gramPolynomial (aa bb cc ab ac bc : ℝ) : ℝ :=
  aa*bb*cc+2*ab*ac*bc-aa*bc^2-bb*ac^2-cc*ab^2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-vector Gaussian band estimates for the angular slicing construction -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def gaussianBandConstant : ℝ := 2*(Real.sqrt (2*Real.pi))⁻¹

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPairBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularized two-vector Gaussian band bounds -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def gaussianPairBandConstant : ℝ :=
  2*gaussianBandConstant+4*gaussianBandConstant^2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLebesgue
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Lebesgue density for the standard Gaussian used in the band estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform
variable {d : ℕ}

noncomputable def gaussianVolumeNormalization (d : ℕ) : ℝ := ((2*Real.pi)^((d:ℝ)/2))⁻¹

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianVectorBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian bands for unnormalized point differences -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianVectorBandConstant : ℝ := 2*(1+gaussianBandConstant)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PublishedLoomisWhitney
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact finite lattice projection input for general-dimensional tube counting

Loomis–Whitney, *An inequality related to the isoperimetric inequality*,
Bull. AMS 55 (1949), 961–962, DOI 10.1090/S0002-9904-1949-09320-5.
The finite lattice consequence is stated explicitly in Balister–Bollobás,
*Projections, entropy and sumsets*, Combinatorica 32 (2012), equation (7),
specialized here to the (n+1) coordinate-deletion projections, an n-uniform cover.
Author manuscript: https://www.memphis.edu/msci/people/pbalistr/projections.pdf
Only this counting specialization is an explicit conditional input.
-/

namespace Falconer
open scoped BigOperators

abbrev dropGridCoordinate {n : ℕ} (i : Fin (n+1)) (z : Fin (n+1) → ℤ) : Fin n → ℤ :=
  fun j => z (i.succAbove j)

def PublishedFiniteLoomisWhitney : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ S : Finset (Fin (n+1) → ℤ),
    S.card^n ≤ ∏ i : Fin (n+1), (S.image (dropGridCoordinate i)).card

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TripleGridRounding
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounding bounded physical point sets in transverse coordinates -/

namespace Falconer
open Set Metric

noncomputable def tripleIntegerBox (L : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(L:ℤ)) (L:ℤ)).product
    ((Finset.Icc (-(L:ℤ)) (L:ℤ)).product (Finset.Icc (-(L:ℤ)) (L:ℤ)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GeneralGridRounding
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded original point sets admit finite transverse lattice approximations -/

namespace Falconer
open Set Metric
variable {n : ℕ}

noncomputable def integerGridBox (n L : ℕ) : Finset (Fin (n+1) → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(L:ℤ)) (L:ℤ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GeneralTransverseCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative general-dimensional transverse tube counting -/

namespace Falconer
open Set Metric
open scoped BigOperators
variable {n : ℕ}

noncomputable def generalTubeCountConstant (d : ℕ) (C : ℝ) : ℝ :=
  2*(d:ℝ)^2*(d.factorial:ℝ)*(C+(d:ℝ)^2)+4

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_IidSampling
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent sampling of direction and point labels

The finite product law below samples the original labels, before their
geometric coordinates are taken. Repeated coordinates therefore retain
their original incidence fibers, as required by `ang:planar-measures`.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators

noncomputable def iidLaw {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (n : ℕ) : Measure (Fin n → X) :=
  Measure.pi (fun _ => (ν : Measure X))

instance instIsProbabilityMeasureForallFinIidLaw {X : Type*} [MeasurableSpace X] (ν : ProbabilityMeasure X) (n : ℕ) :
    IsProbabilityMeasure (iidLaw ν n) := by
  unfold iidLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def iidCount {X : Type*} (A : Set X) {n : ℕ} (ω : Fin n → X) : ℝ :=
  ∑ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (ω i)

noncomputable def iidAverage {X : Type*} (f : X → ℝ) {n : ℕ} (ω : Fin n → X) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, f (ω i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LinearPieces
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of a bounded-scale family of intervals with uniform linear error. -/
namespace Falconer
open Set

noncomputable def dyadicLinearPieces (f : ℝ → ℝ) (a h η : ℝ) (n m : ℕ) : List (ℝ × ℝ) := by
  classical
  exact (dyadicCells a h n).filter fun c =>
    dyadicSlopeVariance f c.1 c.2 (intervalSecantSlope f c.1 c.2) m ≤ η^2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_MonotoneLowpass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Low-pass terms for the decreasing-measure shell argument

The Schwartz Fourier cutoffs represent the low-pass terms of shell
reconstruction. The L¹ bound is uniform in the dyadic cutoff index.
-/

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem sourceShellLowpass_compact (n : ℕ) : HasCompactSupport (sourceShellLowpass n) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((2 : ℝ)^(n+1)))
  intro r hr
  apply sourceShellLowpass_zero
  have hn : ¬ |r| ≤ (2 : ℝ)^(n+1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hr
  exact le_of_lt (lt_of_not_ge hn)

noncomputable def dyadicLowpassSchwartz (n : ℕ) : 𝓢(ℝ, ℂ) :=
  ((sourceShellLowpass_compact n).toSchwartzMap (sourceShellLowpass_smooth n)).postcompCLM
    Complex.ofRealCLM

@[simp] theorem dyadicLowpassSchwartz_apply (n : ℕ) (r : ℝ) :
    dyadicLowpassSchwartz n r = (sourceShellLowpass n r : ℂ) := rfl

noncomputable def dyadicLowKernel (n : ℕ) : ℝ → ℂ :=
  sourceInverseKernel (dyadicLowpassSchwartz n)

theorem dyadicLowKernel_integrable (n : ℕ) : Integrable (dyadicLowKernel n) :=
  sourceInverseSchwartz_integrable _

theorem dyadicLowKernel_continuous (n : ℕ) : Continuous (dyadicLowKernel n) :=
  sourceInverseKernel_continuous _ (dyadicLowpassSchwartz n).integrable

noncomputable def dyadicLowTerm (n : ℕ) (τ : FiniteMeasure ℝ) :
    Lp (α := ℝ) ℂ 1 volume :=
  (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1 (dyadicLowKernel n)
    (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) τ).1).toLp
      (kernelMeasureConvolution (dyadicLowKernel n) τ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NearPinDeletion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Near-parent pins are removed with their original source-cell weights -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X Y ι : Type*} [MeasurableSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

noncomputable def nearPinPairs (I : Finset ι) (Q : ι → Set X) (c : ι → Y) (r : ℝ) :
    Set (X × Y) := ⋃ i ∈ I, Q i ×ˢ ball (c i) r

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SamplingGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite planar query balls for simultaneous iid estimates

Rounding one point of a ball to the spatial mesh and rounding its radius
up to an integer mesh multiple gives a query ball with radius at most
eight times the original radius. The number of queries is polynomial in
the reciprocal mesh. This is the finite-grid step in `ang:sample-caps`.
-/

namespace Falconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def planarGrid (L : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(L : ℤ)) (L : ℤ))

noncomputable def planarQueries (L H : ℕ) : Finset ((Fin 2 → ℤ) × ℤ) :=
  planarGrid L ×ˢ Finset.Icc 1 (H : ℤ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarSampling
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Original labels, slope coordinates and prescribed strip covers

These adapters connect the two uniform sampling stages to the exact finite
Furstenberg obstruction. Every strip list remains indexed by its original
direction label, including when slope coordinates coincide.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def incidentLabels {X W : Type*} (E : X → W → Prop)
    {n : ℕ} (ω : Fin n → W) (x : X) : Finset (Fin n) :=
  Finset.univ.filter (fun i => E x (ω i))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RobustProjectionSets
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A good original direction works for every later large point subset.
The output is an actual separated projected set, with original witnesses,
explicit regularity cost and a quantitative cardinality lower bound. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def projectedSubsetSampleConstant
    (N : ℕ) (s t KI KP ρ : ℝ) : ℝ :=
  let C := (2*(2*projectionEnergyBudget N s t KI KP)/ρ)*(2/ρ)*(2:ℝ)^s
  let γ := (1/(2:ℝ)^N)/4
  2*(2*(((Real.exp 1-1)*(C*(4:ℝ)^s)+(1-10*Real.log γ))*(8:ℝ)^s))^2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionSampleBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial costs for the robust projection step. These bounds
keep every loss explicit before the dyadic exponential absorption. -/
namespace Falconer

noncomputable def projectionGapConstant (κ : ℝ) : ℝ :=
  1+2*(1+2/(1-(2:ℝ)^(-κ)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_InnerProfileGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inward rounding of profile intervals to a fixed finite scale grid. -/
namespace Falconer

noncomputable def profileGridLeft (n : ℕ) (a : ℝ) : ℝ := (⌈(n : ℝ)*a⌉ : ℝ)/(n : ℝ)
noncomputable def profileGridRight (n : ℕ) (b : ℝ) : ℝ := (⌊(n : ℝ)*b⌋ : ℝ)/(n : ℝ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGridCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite interval accounting after inward rounding to the block grid. -/
namespace Falconer

noncomputable def innerProfileCell (n : ℕ) (c : ℝ × ℝ) : ℝ × ℝ :=
  (profileGridLeft n c.1,profileGridRight n (c.1+c.2)-profileGridLeft n c.1)

@[simp] theorem innerProfileCell_end (n : ℕ) (c : ℝ × ℝ) :
    (innerProfileCell n c).1+(innerProfileCell n c).2 = profileGridRight n (c.1+c.2) := by
  simp [innerProfileCell]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfilePrefix
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prefix clipping for the finite low-slope merge algorithm. At most one
original interval is shortened; an undersized residual costs one minimum length. -/
namespace Falconer

noncomputable def clipProfilePrefix (u r : ℝ) : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => []
  | c::S => if c.1+c.2 ≤ u then c::clipProfilePrefix u r S
      else if r ≤ u-c.1 then [(c.1,u-c.1)] else []

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileCellFamily
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invariants for the finite profile-merging recursion. The original equal
width cells are retained as witnesses when their active prefixes are shortened. -/
namespace Falconer
open Set

structure ProfileCellFamily (f : ℝ → ℝ) (H r η m b : ℝ) (S : List (ℝ × ℝ)) : Prop where
  ordered : S.Pairwise (fun c d => c.1+H ≤ d.1)
  bounds : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+H ≤ m ∧ r ≤ c.2 ∧ c.2 ≤ H ∧ c.1+c.2 ≤ b
  linear : ∀ c ∈ S, ∀ x ∈ Icc c.1 (c.1+H), |intervalSecantError f c.1 H x| ≤ η^2*H

structure StructuredProfilePieces (f : ℝ → ℝ) (r θ s b : ℝ) (S : List (ℝ × ℝ)) : Prop where
  ordered : S.Pairwise (fun c d => c.1+c.2 ≤ d.1)
  bounds : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+c.2 ≤ b ∧ r ≤ c.2
  alternatives : ∀ c ∈ S,
    (s ≤ intervalSecantSlope f c.1 c.2 ∧
      ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ θ*c.2) ∨
    (intervalSecantSlope f c.1 c.2 = s ∧
      ∀ x ∈ Icc c.1 (c.1+c.2), -θ*c.2 ≤ intervalSecantError f c.1 c.2 x)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PlanarCriticalPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical finite planar potential with the exact linear depth loss.
This is used to control the distribution of cells along a selected tube. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def planarCriticalConstant (N : ℕ) (t : ℝ) : ℝ :=
  1+(2:ℝ)^t*(1+(N:ℝ)*(2:ℝ)^t)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarScalarGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual scalar grid coordinates for a planar finite set. Rounding is
injective below the separation scale and coordinate counts are exactly the
original scalar cell counts. -/
namespace Falconer

noncomputable def scalarGridFloor (δ x : ℝ) : ℝ := δ*(⌊x/δ⌋:ℝ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientClosure
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite additive and multiplicative closure used in the scalar
sum-product argument. Each stage has an explicit coefficient radius. -/
namespace Falconer
open scoped Pointwise

noncomputable def scalarCoefficientClosure (S : Finset ℝ) : ℕ → Finset ℝ
  | 0 => S
  | n+1 => let T := scalarCoefficientClosure S n
    (T ∪ -T) ∪ ((T+T) ∪ (T*T))

def scalarCoefficientRadius (M : ℕ) : ℕ → ℕ
  | 0 => M+1
  | n+1 => 2*(scalarCoefficientRadius M n)^2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial losses for finitely many scalar sum-product
operations. No generation or density assertion is assumed here. -/
namespace Falconer

def scalarCoefficientBudget (M : ℕ) (K : ℝ) : ℕ → ℝ
  | 0 => K
  | n+1 => 32768*((scalarCoefficientRadius M n : ℝ)+4)*(scalarCoefficientBudget M K n)^8

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarGridFibers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar dyadic cell fibers for the porous grouping step. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def scalarGridFiber (η z : ℝ) (E : Finset ℝ) (k : ℤ) : Finset ℝ :=
  E.filter fun x => ⌊(x-z)/η⌋ = k

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCorrelatedWeights
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same coefficient is used at every porous scale. The following
 finite Jensen estimate averages products without any independence
 assumption on the exceptional sets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def scalarCollisionWeight {β : Type*} (L : ℝ) (G : Finset β) (b : β) : ℝ :=
  if b ∈ G then L⁻¹ else 1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarLogAverages
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient averages for the multiscale porous argument. -/
namespace Falconer

noncomputable def scalarAverage {β : Type*} (B : Finset β) (f : β → ℝ) : ℝ :=
  (∑ b ∈ B, f b)/(B.card : ℝ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchingSuffix
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Minimal heavy suffixes for the porous level-bunching construction.
 Trimming a short terminal segment has a controlled entropy cost. -/
namespace Falconer

 def scalarBunchTrim (r : ℕ) : ℕ := if r ≤ 1000 then 0 else r/100

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarBunchingLedger
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite greedy ledger for porous bunches. Its intervals partition
 a terminal range, and every omitted tail has a controlled weight loss. -/
namespace Falconer

structure ScalarBunch where
  start : ℕ
  cut : ℕ
  stop : ℕ
  start_lt_cut : start < cut
  cut_le_stop : cut ≤ stop

inductive ScalarBunchChain : ℕ → ℕ → List ScalarBunch → Prop
  | nil (n : ℕ) : ScalarBunchChain n n []
  | cons (b : ScalarBunch) {lo : ℕ} {bs : List ScalarBunch}
      (h : ScalarBunchChain b.start lo bs) : ScalarBunchChain b.stop lo (b :: bs)

structure ScalarBunchGood (w : ℕ → ℝ) (theta : ℝ) (b : ScalarBunch) : Prop where
  loss : (∑ i ∈ Finset.Ico b.cut b.stop, w i) ≤ theta*((b.stop-b.start:ℕ):ℝ)/100
  retained : (99/100:ℝ)*theta*((b.stop-b.start:ℕ):ℝ) ≤ ∑ i ∈ Finset.Ico b.start b.cut, w i
  trim_budget : 100*(b.stop-b.cut) ≤ b.stop-b.start
  gap : (b.stop = b.cut ∧ b.stop-b.start ≤ 1000) ∨ b.stop-b.start ≤ 200*(b.stop-b.cut)

 theorem ScalarBunchChain.start_le {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) : lo ≤ N := by
  induction h with
  | nil n => exact le_rfl
  | cons b h ih => exact ih.trans (b.start_lt_cut.le.trans b.cut_le_stop)


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPartialSums
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Approximate arithmetic progressions from nearly equal increments. -/
namespace Falconer

noncomputable def scalarPartialSum (d : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, d i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSwitchSums
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite sum identities for changing selected coordinates. All
 switched sums remain in the same fixed-fold sumset of original points. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

noncomputable def scalarSwitchSum {ι : Type*} (I F : Finset ι) (p q : ι → ℝ) : ℝ :=
  ∑ i ∈ I, if i ∈ F then q i else p i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarBinaryBranch
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonporous binary state produces many separated children in a
 fixed-fold sumset. Only actual bit updates of original words are used. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 def ScalarBinaryTail {N : ℕ} (n : ℕ) (w : Fin N → Bool) : Prop :=
  ∀ j : Fin N, n ≤ (j:ℕ) → w j = false

noncomputable def scalarBinaryStep {N k : ℕ} (c : Fin k → Fin N → Bool)
    (n : Fin N) (F : Finset (Fin k)) : Fin k → Fin N → Bool :=
  fun i => if i ∈ F then Function.update (c i) n true else c i

noncomputable def scalarBinarySum {N k : ℕ} (f : (Fin N → Bool) → ℝ)
    (c : Fin k → Fin N → Bool) : ℝ := ∑ i, f (c i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchTransfer
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locality facts for iterating bunch trims from fine to coarse scales. -/
namespace Falconer

 theorem ScalarBunchChain.mem_bounds {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) :
    ∀ b ∈ bs, lo ≤ b.start ∧ b.stop ≤ N := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    intro c hc
    rcases List.mem_cons.mp hc with heq | hc
    · subst c
      exact ⟨h.start_le,le_rfl⟩
    · have hh := ih c hc
      exact ⟨hh.1,hh.2.trans (b.start_lt_cut.le.trans b.cut_le_stop)⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The realized ledger, ordered from fine to coarse scales, is the
 separated tree consumed by the porous projection estimate. -/
namespace Falconer

def scalarBunchBoundary (lo : ℕ) (bs : List ScalarBunch) (i : ℕ) : ℕ :=
  (bs.map ScalarBunch.stop).getD i lo

 theorem ScalarBunchChain.boundary_zero {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) : scalarBunchBoundary lo bs 0 = top := by
  cases h <;> simp [scalarBunchBoundary]

 theorem ScalarBunchChain.boundary_edges {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) : ∀ i (hi : i < bs.length),
    scalarBunchBoundary lo bs i = (bs[i]).stop ∧
      scalarBunchBoundary lo bs (i+1) = (bs[i]).start := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    intro i hi
    cases i with
    | zero =>
      constructor
      · simp [scalarBunchBoundary]
      · simpa only [scalarBunchBoundary,List.map_cons,List.getD_cons_succ,List.getElem_cons_zero]
          using h.boundary_zero
    | succ i =>
      simpa only [scalarBunchBoundary,List.map_cons,List.getD_cons_succ,List.getElem_cons_succ]
        using ih i (show i < bs.length by simpa using hi)

 theorem ScalarBunchChain.boundary_bounds {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) (i : ℕ) :
    lo ≤ scalarBunchBoundary lo bs i ∧ scalarBunchBoundary lo bs i ≤ top := by
  by_cases hi : i < bs.length
  · rw [(h.boundary_edges i hi).1]
    have hb := h.mem_bounds bs[i] (List.getElem_mem hi)
    exact ⟨hb.1.trans ((bs[i]).start_lt_cut.le.trans (bs[i]).cut_le_stop),hb.2⟩
  · have hx : (bs.map ScalarBunch.stop).length ≤ i := by simpa using Nat.le_of_not_gt hi
    simp only [scalarBunchBoundary,List.getD_eq_default _ _ hx]
    exact ⟨le_rfl,h.start_le⟩

 theorem scalarBunchValue_at {α : Type*} (f : ScalarBunch → α) (z : α)
    {bs : List ScalarBunch} {i : ℕ} (hi : i < bs.length) :
    (bs.map f).getD i z = f bs[i] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCompressedLevels
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Consecutive original blocks collapse to a separated level. Its gap is
 controlled by the final original block, so prescribed porous endpoints
 supply the separation needed after bunching. -/
namespace Falconer.Regularization

def scalarCompressedBranch (e k : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (e j) (e (j+1)), k i

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchSizes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing group sizes from the greedy bunch lengths. A threshold 2P
 gives groups of size 2^(P length), with a closed formula for total gain. -/
namespace Falconer

def scalarBunchGroup (P : ℕ) (b : ScalarBunch) : ℕ := 2^(P*(b.stop-b.start))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarNonporousPowers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale arithmetic for a subsequence of nonporous dyadic blocks. -/
namespace Falconer.Regularization

noncomputable def scalarSelectedScale (B : ℕ) (g : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then (1/2:ℝ)^(B*g 0) else (1/2:ℝ)^(B*(g (i-1)+1))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarLevelEnumeration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerating selected scalar blocks in geometric order, with a final
 sentinel for the gap after the last selected block. -/
namespace Falconer.Regularization
open scoped Pointwise

noncomputable def scalarNonporousLevels (M B C : ℕ) (branch n : ℕ → ℕ) : Finset ℕ :=
  (Finset.range M).filter fun i => branch i ≠ 0 ∧ B*(i+1) ≤ n i+C

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPorousLevels
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual porous/nonporous partition. Collapsed levels have no
 geometric constraint and can be normalized to their coarser endpoint. -/
namespace Falconer.Regularization

def scalarEffectiveLevel (B : ℕ) (k n : ℕ → ℕ) (i : ℕ) : ℕ :=
  if k i = 0 then B*i else n i

noncomputable def scalarPorousLevels (M B C : ℕ) (k n : ℕ → ℕ) : Finset ℕ :=
  (Finset.range M).filter fun i => k i = 0 ∨ n i+C < B*(i+1)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarClusterTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated cluster trees retain all leaves in each terminal fiber.
 Their common terminal cardinality multiplies every level of the gain. -/
namespace Falconer

structure ScalarClusterTree (δ : ℝ) (N : ℕ) where
  nodes : ℕ → Finset ℝ
  children : ℕ → ℝ → Finset ℝ
  points : ℕ → ℝ → Finset ℝ
  branching : ℕ → ℕ
  radius : ℕ → ℝ
  gap : ℕ → ℝ
  branch_pos : ∀ n < N, 0 < branching n
  radius_ge : ∀ n < N, δ ≤ radius n
  gap_pos : ∀ n < N, 0 < gap n
  gap_gt : ∀ n < N, 5*radius n < gap n
  child_subset : ∀ n < N, ∀ x ∈ nodes (n+1), children n x ⊆ nodes n
  child_card : ∀ n < N, ∀ x ∈ nodes (n+1), (children n x).card = branching n
  child_sep : ∀ n < N, ∀ x ∈ nodes (n+1), ∀ y ∈ children n x,
    ∀ z ∈ children n x, y ≠ z → gap n ≤ |y-z|
  child_bound : ∀ n < N, ∀ x ∈ nodes (n+1), ∀ y ∈ children n x,
    ∀ a ∈ points n y, |a-y| ≤ radius n
  parent_eq : ∀ n < N, ∀ x ∈ nodes (n+1), points (n+1) x = (children n x).biUnion (points n)
  leaf_size : ℕ
  leaf_pos : 0 < leaf_size
  leaf_card : ∀ x ∈ nodes 0, (points 0 x).card = leaf_size
  leaf_sep : ∀ x ∈ nodes 0, ∀ u ∈ points 0 x, ∀ v ∈ points 0 x,
    u ≠ v → δ ≤ |u-v|

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBinaryParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit fixed-fold parameters for the nonporous binary construction.
 Their logarithmic branching approaches the original block width. -/
namespace Falconer

def scalarBinaryBranchCount (B C : ℕ) : ℕ := 2^(B-2*C)
def scalarBinaryCopyBound (B C : ℕ) : ℕ := 72*scalarBinaryBranchCount B C*2^C

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarNormalizedProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small projections survive the precise coefficient density zoom.
 The budget is explicit and uses only a fixed number of scalar operations. -/
namespace Falconer
open scoped Pointwise

def scalarNormalizedBaseBudget (M : ℕ) (K : ℝ) : ℝ :=
  1+K+45*(2*K)^7+(2*(M:ℝ)+3)*scalarCoefficientBudget 1 K 3

def scalarNormalizedProjectionBudget (M : ℕ) (K : ℝ) : ℝ :=
  scalarCoefficientBudget (M+2) (scalarNormalizedBaseBudget M K) 5

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarNormalizedLogBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalization cost grows at most polynomially with the weak
 Frostman constant and the original projection bound. -/
namespace Falconer

def scalarNormalizedBaseConstant : ℝ := 5762+2*scalarCoefficientBudget 1 1 3

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarNormalizationCost
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eliminate the selected radius from the projection budget: its entire
 cost is controlled by logarithms of the original two weak constants. -/
namespace Falconer

noncomputable def scalarNormalizationRadius (κ K : ℝ) : ℕ := ⌈2*K^(1/κ)⌉₊

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarInitialGrowth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative projection growth before the initial regularization.
 Both nonporous and porous alternatives are compared to the original set. -/
namespace Falconer
open scoped Pointwise

def scalarBinaryCopies (B C : ℕ) : ℕ :=
  (2*scalarBinaryCopyBound B C+1)*scalarBinaryBranchCount B C

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionRatioGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry of the fractional-linear direction map generated by two
projection bases. All constants depend only on their separation. -/
namespace Falconer

noncomputable def projectionRatio (a b y : ℝ) : ℝ := (y-a)/(b-y)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_RegularGraphCosts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial losses in the refined graph obstruction, specialized to a
single weak scale parameter. -/
namespace Falconer

noncomputable def regularGraphCost (M : ℕ) : ℝ :=
  1+1024*(2*(M:ℝ)+3)^2+4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2+
    2*(1+4*(M:ℝ))^2+2*(M:ℝ)^2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileStepBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One explicit budget for the two branches of the endpoint scale product. -/
namespace Falconer

noncomputable def profileStepBudget (H G W : ℝ) : ℝ := 1024*W^2*H^3*G

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileIntervalChain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition of actual profile interval estimates. Every splitting
step uses the proved endpoint construction and its explicit next budget. -/
namespace Falconer
open Set Regularization
open scoped BigOperators

noncomputable def profileBudgetSequence (H G W : ℝ) : ℕ → ℝ
  | 0 => W
  | n+1 => profileStepBudget H G (profileBudgetSequence H G W n)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileHighMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A profile with large total growth spends positive total length in the
linear intervals whose slope exceeds a prescribed intermediate threshold. -/
namespace Falconer
open Set

noncomputable def profileHighLength (f : ℝ → ℝ) (u : ℝ) (S : List (ℝ × ℝ)) : ℝ :=
  ((S.filter fun c => u ≤ intervalSecantSlope f c.1 c.2).map Prod.snd).sum

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGainAccounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Add normal and good interval gains while charging the actual chord-error
length and one fixed weak loss per interval. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def profileGainExponent (f : ℝ → ℝ) (u s η a loss N : ℝ)
    (c : ℝ × ℝ) : ℝ :=
  N*((s-a)*c.2+η*(if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0)-loss)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockCellNormalGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal estimate evaluated directly on a selected real profile cell. -/
namespace Falconer
open Set Regularization

noncomputable def profileGeometryConstant (K B : ℕ) (W A : ℝ) : ℝ :=
  100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OriginalWeakCosts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All preparation costs fit one fixed polynomial. This converts the
original block-incidence estimate to the published weak-power conclusion. -/
namespace Falconer

noncomputable def originalIncidenceCost (B : ℕ) : ℝ :=
  max (165888*(4*(2:ℝ)^B)*(2*(B:ℝ)+13)*(64*(2:ℝ)^B+1)^2)
    (162*(64*(2:ℝ)^B+1)^2*(4*(2:ℝ)^B)^2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuadraticDifferential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differential of the quadratic-to-gnomonic coordinate change

The differential is a scalar multiple of the identity plus one radial
rank-one term. These are actual derivatives of the coordinate map, not
assumed Jacobian data.
-/

namespace Falconer

noncomputable def quadraticRadialFactor (s : ℝ) : ℝ :=
  Real.sqrt (1-s/4) / (1-s/2)

noncomputable def quadraticRadialDerivative (s : ℝ) : ℝ :=
  (6-s) / (16 * Real.sqrt (1-s/4) * (1-s/2)^2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FourStationaryPhases
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The four actual radial phases in a far spherical product -/

namespace Falconer

noncomputable def stationaryPhase (t : ℝ) : ℂ := Complex.exp (Complex.I*(t : ℂ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_LocalStationaryJets
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local mixed derivative bounds on the actual stationary chart

The chart is smooth on an open pole patch. These lemmas localize the
vertical Laplacian estimate to that patch, without extending the chart
across its singularities.
-/

namespace Falconer
open Set
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable local instance instNormedSpaceRealContinuousLinearMapIdComplex_solutions_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance
noncomputable local instance instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SeparatedJets
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite separated symbols and their actual derivatives

The two external parameters remain in different factors. Directional
derivatives use the ordinary product rule, so taking finitely many chart
jets never introduces a joint endpoint symbol.
-/

namespace Falconer
open scoped ContDiff

variable {X Y E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

structure SmoothSeparation (X Y E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  index : Type
  finite : Fintype index
  left : index → X → E → ℂ
  right : index → Y → E → ℂ
  left_smooth : ∀ i x, ContDiff ℝ ∞ (left i x)
  right_smooth : ∀ i y, ContDiff ℝ ∞ (right i y)

attribute [instance] SmoothSeparation.finite

namespace SmoothSeparation

noncomputable def value (S : SmoothSeparation X Y E) (x : X) (y : Y) (z : E) : ℂ :=
  ∑ i : S.index, S.left i x z*S.right i y z

end SmoothSeparation
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SignedRadialKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radial decay with both actual stationary signs

The two Boolean indices are the outgoing and incoming terms of the full
sphere expansion. The original amplitude remains the argument in all
four cases; antipodal conjugation is internal to its signed coefficient.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

def stationarySign (outgoing : Bool) : ℝ := if outgoing then 1 else -1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetSeparation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite normalized endpoint factors for the actual inverse

The original individual-mask jets remain in the smooth endpoint factors.
All inverse-radius powers are kept in a separate scalar weight per term.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace SmoothSeparation
variable {X Y E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def scaleTerms (S : SmoothSeparation X Y E) (c : S.index → ℂ) :
    SmoothSeparation X Y E where
  index := S.index
  finite := S.finite
  left := fun i x z => c i*S.left i x z
  right := S.right
  left_smooth := fun i x => contDiff_const.mul (S.left_smooth i x)
  right_smooth := S.right_smooth

end SmoothSeparation

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLocalBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Band mass inside a fixed neighborhood of a transverse row -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

noncomputable def gaussianLocalBandConstant (n : ℕ) (ρ : ℝ) : ℝ :=
  gaussianVolumeNormalization (n+1)*
    Real.exp (-(1/2:ℝ)*(1+(n+1:ℝ)*(2*ρ))^2)*2*(2*ρ)^n

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OuterRootGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual outer graph coefficient combined with the two recursive roots -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

noncomputable def outerGraphLoss (m : ℕ) (lam σ : ℝ) : ℝ :=
  (1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*σ+4*(((m+3:ℕ):ℝ)+1)*lam

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_Published
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published radial input for the planar Falconer application

The only input isolated here is the planar specialization of Orponen,
*On the dimension and smoothness of radial projections*, Analysis & PDE
12 (2019), 1273–1294, proof of Theorem 1.13, equations (3.5)–(3.6).
The parameters used by the application are
`s = 1 + δ / 2`, `t = 1 - δ / 4`, and `p = 1 + δ / 8`.
They satisfy the strict inequalities in (3.5).  Orponen uses a distance
weighted source measure; on disjoint compact supports that weight and its
inverse are bounded, so finiteness of the moment is unchanged.

Prepared root measures follow from this radial moment estimate.
-/

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

/-- The precise finite-energy consequence of the published radial theorem used
in the planar application.  The source and pin laws may be interchanged. -/
def PublishedPlanarRadialMoment : Prop :=
  ∀ (α β : ProbabilityMeasure Plane) (δ : ℝ), 0 < δ → δ < 1 →
    IsCompact (α : Measure Plane).support →
    IsCompact (β : Measure Plane).support →
    Disjoint (α : Measure Plane).support (β : Measure Plane).support →
    rieszEnergy α (1 + δ / 2) < ∞ →
    rieszEnergy β (1 - δ / 4) < ∞ →
    (∫⁻ x, (sourceDensityNorm (1 + δ / 8)
      ((α : Measure Plane).map (sourceRadialUnit x))) ^ (1 + δ / 8) ∂β) < ∞


end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RestorationSeries
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summability of the actual cap, class and descriptor deletion costs -/

namespace Falconer
open Filter
open scoped ENNReal Topology

noncomputable def restorationError (Cw Ccap c lam σ : ℝ) (k₁ k₂ N : ℕ) : ℝ :=
  Cw * (Ccap*((2:ℝ)^N)^(-c) + 2*((2:ℝ)^N)^(-2:ℝ) +
    ((N:ℝ)+1)^k₁*((2:ℝ)^N)^(-lam) + ((N:ℝ)+1)^k₂*((2:ℝ)^N)^(-lam) +
    4*((N:ℝ)+1)^2*((2:ℝ)^N)^(-σ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TripleGramStability
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stability of the three-direction Gram determinant under projection -/

namespace Falconer
open scoped BigOperators

def determinantTerms (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 6 → ℝ :=
  ![A 0 0*A 1 1*A 2 2,-(A 0 0*A 1 2*A 2 1),-(A 0 1*A 1 0*A 2 2),
    A 0 1*A 1 2*A 2 0,A 0 2*A 1 0*A 2 1,-(A 0 2*A 1 1*A 2 0)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_OneScaleGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed normalization and collision widths for the three-interval argument -/

namespace Falconer

noncomputable def cellContraction (d : ℕ) : ℝ := 1/(4*(Real.sqrt d+1))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CommonTripleIncidence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common point incidence of three original direction labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

def commonTripleRelation (E : Set (X × W)) : Set (X × (W × W × W)) :=
  {p | (p.1,p.2.1) ∈ E ∧ (p.1,p.2.2.1) ∈ E ∧ (p.1,p.2.2.2) ∈ E}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CommonTupleIncidence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common incidence of an arbitrary finite tuple of original pins -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

def commonTupleRelation (k : ℕ) (E : Set (X × W)) : Set (X × (Fin k → W)) :=
  {p | ∀ i, (p.1,p.2 i) ∈ E}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteBallPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneously enforcing the finitely many slice ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]

def finiteBallGood (μ : Measure X) (r : ι → ℝ) (B : ι → ℝ≥0∞) : Set X :=
  {x | ∀ i, μ (ball x (2*r i)) ≤ B i}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RadialBlockDepths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A dyadic block schedule with two initial blocks reserved for freezing -/

namespace Falconer

def radialBlockSize (N J : ℕ) : ℕ := N/(J+2)

def radialBlockDepth (N J j : ℕ) : ℕ :=
  N-J*radialBlockSize N J+j*radialBlockSize N J

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DensityTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Truncation of radial densities

The integer-cap step `prep:integer-caps` deletes pairs on which either
radial density exceeds a threshold. These lemmas estimate the deleted
original product mass by the Lp moments and bound every remaining fiber
by the threshold times the angular reference measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

/-- The bad pairs for one orientation of a radial kernel. -/
def densityFailure {X Y A : Type*} (f : X × A → ℝ≥0∞)
    (r : X × Y → A) (T : ℝ≥0∞) : Set (X × Y) :=
  {z | T < f (z.1, r z)}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiberDensityPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Density pruning uses the original fibers in every retained cell -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

noncomputable def fiberDensityBad (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (θ : ℝ≥0∞) : Set (P × X) :=
  G ∩ ⋃ i ∈ I, {p | μ (Q i ∩ Prod.mk p ⁻¹' G) < θ*μ (Q i)} ×ˢ Q i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FirstExclusionMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Charging each pair only at its first exclusion scale -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

def firstExclusion (E : ℕ → Set X) (n : ℕ) : Set X :=
  E n \ ⋃ j ∈ Finset.range n, E j

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MeanProbability
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean probability of the two original endpoint laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

noncomputable def meanProbability (μ ν : ProbabilityMeasure X) : ProbabilityMeasure X := by
  let ρ : Measure X := (2:ℝ≥0∞)⁻¹ • ((μ : Measure X)+(ν : Measure X))
  have : IsProbabilityMeasure ρ := by
    constructor
    simp only [ρ,Measure.smul_apply,Measure.add_apply,measure_univ,smul_eq_mul]
    rw [show (1:ℝ≥0∞)+1=2 by norm_num]
    exact ENNReal.inv_mul_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞)
  exact ⟨ρ,this⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MultiscaleDensityPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous density pruning at finitely many endpoint depths -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

noncomputable def multiscaleFiberBad (μ : Measure X) (G : Set (P × X))
    (Q : ℕ → ι → Set X) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ) : Set (P × X) :=
  ⋃ j ∈ Finset.range (J+1), fiberDensityBad μ G (Q j) (I j) θ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlateScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic powers and the earlier scale used by the coarse plate filter -/

namespace Falconer
open Filter
open scoped Topology

noncomputable def plateScale (j : ℕ) : ℝ := (2:ℝ)^(-(j:ℝ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlateAffineBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-width affine slab bounds for the original coarse-filter fibers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def coarseSlabConstant (j₀ : ℕ) (b : ℝ) : ℝ :=
  max ((plateScale j₀)^(-b)) (2*(2:ℝ)^b)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadialLosses
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous fixed losses for the single-scale weak radial theorem -/

namespace Falconer

structure WeakRadialLosses (n : ℕ) (ℓ ζ : ℝ) where
  J : ℕ
  e : ℝ
  f : ℝ
  τ : ℝ
  η : ℝ
  lam : ℝ
  u : ℝ
  ε : ℝ
  c : ℝ
  J_pos : 0 < J
  e_pos : 0 < e
  f_pos : 0 < f
  η_pos : 0 < η
  η_le : η ≤ 1/2
  lam_pos : 0 < lam
  u_pos : 0 < u
  ε_pos : 0 < ε
  c_pos : 0 < c
  ε_lt_lam : ε < lam
  regularization_gap : 2*((n:ℝ)+2)*lam < τ
  count_gap : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u
  incidence_gap : c*((n:ℝ)+1) < u
  slab_gap : c*((n:ℝ)+1) < η*ζ-ε
  near_gap : ε < (n:ℝ)/((J:ℝ)+2)
  cap_gap : (J:ℝ)*(e+f)-((n:ℝ)/(n+1))*
    ((n:ℝ)-((n:ℝ)+5)*lam-2*((n:ℝ)+1)/((J:ℝ)+2)) < -ℓ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PointRieszPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Riesz potential bound from small balls at one fixed center -/
namespace Falconer
open Set Metric MeasureTheory Filter PlanarFalconer
open scoped ENNReal Topology
variable {d : ℕ}

noncomputable def rieszSmallBallBound (s C u : ℝ) : ℝ≥0∞ :=
  1 + ENNReal.ofReal ((1/2:ℝ)^(-u)*C*2^s) *
    ∑' n : ℕ, (ENNReal.ofReal ((1/2:ℝ)^(s-u)))^n

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileSuffixMinimum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The future minimum of a scale profile on the unit interval -/

namespace Falconer
open Set
open scoped NNReal

noncomputable def profileSuffixMinimum (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  sInf (f '' Icc u 1)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ThreeIntervalData
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual four dyadic depths and three collision factors -/

namespace Falconer
open scoped ENNReal BigOperators

def threeIntervalDepth (a b N j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 1 then a else if j = 2 then b else N

noncomputable def threeIntervalFactor (a b N J : ℕ) (q c η : ℝ) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^a)^(-q))
  else if j = 1 then ENNReal.ofReal ((1/(2:ℝ)^((b-a)-J))^(q+c))
  else ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(N-b))^(-q))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_UniformProfileContact
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform contact intervals for almost Frostman regularization profiles -/

namespace Falconer
open Set Filter
open scoped NNReal Topology

def RobustProfileContact (f : ℝ → ℝ) (q t τ γ : ℝ) : Prop :=
  ∃ A B : ℝ, γ ≤ A ∧ A+γ ≤ B ∧ B+γ ≤ 1 ∧ B+γ ≤ 2*A ∧
    (∀ w ∈ Icc 0 A, q*w-τ*(B-A) ≤ f w) ∧
    (∀ w ∈ Icc A B, t*(w-A)-τ*(B-A) ≤ f w-f A) ∧
    (∀ w ∈ Icc B 1, q*(w-B)-τ*(B-A) ≤ f w-f B)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_MonotoneShellCriterion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Monotone scalar shell reconstruction

This is the analytic reconstruction needed in all dimensions. The measures
remain one-dimensional original-distance pushforwards. Decreasing measures
may approach their limit arbitrarily slowly; only the approximating shell
errors and shell energies are summable.
-/

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

noncomputable def movingShellL1Error (α τ : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    Lp (α := ℝ) ℂ 1 volume :=
  shellL1Error (α n) τ n

noncomputable def monotoneVariationTerm (α : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    Lp (α := ℝ) ℂ 1 volume :=
  dyadicLowTerm (n+1) ⟨(α n : Measure ℝ) - α (n+1), inferInstance⟩ -
  dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n+1), inferInstance⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMomentWeights
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dyadic weights of the actual point and direction pair moments -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianFrostmanFactor (h : ℕ) (s : ℝ) : ℝ :=
  1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-s))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_DyadicSliceSelection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a slice directly from the two original finite-scale ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def gaussianPruningRadius {N : ℕ} (g : Fin (N+1)) : ℝ :=
  (1/(2:ℝ)^g.val)/2

noncomputable def gaussianPruningWeight (h : ℕ) (s : ℝ) {N : ℕ} (g : Fin (N+1)) : ℝ :=
  ((2:ℝ)^g.val)^((h:ℝ)-s)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianThreshold
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform positive incidence threshold on the bounded parameter box -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

noncomputable def gaussianSelectionThreshold (h : ℕ) (K Z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/(4*K*(2*Z)^h))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianTruncatedTriple
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A three-band bound that includes singular triples -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianTripleBandConstant : ℝ :=
  2*gaussianBandConstant^2+8*gaussianVolumeNormalization 3

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing the retained original-label slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def normalizedSliceLaw (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) : ProbabilityMeasure X :=
  ⟨(μ univ)⁻¹ • μ, ⟨by
    rw [Measure.smul_apply,smul_eq_mul,ENNReal.inv_mul_cancel hμ (measure_ne_top μ univ)]⟩⟩

end Falconer

end OAI
end


