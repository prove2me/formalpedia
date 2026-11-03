-- Prove2me | Definitions.Def_OAIQ093D010
-- name    : OAIQ093D010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:02:43.740828+00:00
-- url     : https://prove2.me/theorems/7ac591a2-d554-4604-91c8-40a9d8eb2220
-- title:
--   Definitions bundle OAIQ093D010 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 415 declarations of OpenAI's Lean: 177 definitions, 27 instances and 211 theorems. The definitions and types are `OAI.PolycyclicRecognition.cartanGeneratorPool`, `OAI.PolycyclicRecognition.cartanNilshadowEquiv`, `OAI.PolycyclicRecognition.centerQuotientCocycle`, `OAI.PolycyclicRecognition.centeredL2Cocycle`, `OAI.PolycyclicRecognition.centralLayerTensorSurjection`, `OAI.PolycyclicRecognition.centralLayersAction`, `OAI.PolycyclicRecognition.chartOccupationPoint`, `OAI.PolycyclicRecognition.coarseGroupRingCohomologyIso`, `OAI.PolycyclicRecognition.coefficientComparisonSequenceMap`, `OAI.PolycyclicRecognition.coefficientNaturalCochainMap`, `OAI.PolycyclicRecognition.cofiberCochainCokernelIso`, `OAI.PolycyclicRecognition.cofiberCochainProjection`, `OAI.PolycyclicRecognition.cofiberCochainSequence`, `OAI.PolycyclicRecognition.cokernelProjectiveResolution`, `OAI.PolycyclicRecognition.compactWeightedNorm`, `OAI.PolycyclicRecognition.compactWordCost`, `OAI.PolycyclicRecognition.compactWordLength`, `OAI.PolycyclicRecognition.complexDerivationRealPart`, `OAI.PolycyclicRecognition.complexificationNormedLie`, `OAI.PolycyclicRecognition.conjugationCochainEquiv`, `OAI.PolycyclicRecognition.conjugationCoefficientCochainsIso`, `OAI.PolycyclicRecognition.conjugationCohomologyIso`, `OAI.PolycyclicRecognition.conjugationDifferentialLinearEquiv`, `OAI.PolycyclicRecognition.continuousComplexifiedEnd`, `OAI.PolycyclicRecognition.controlledChainSubrepresentation`, `OAI.PolycyclicRecognition.controlledCochainHomotopy`, `OAI.PolycyclicRecognition.controlledCochainHomotopyEquiv`, `OAI.PolycyclicRecognition.controlledCohomologyIso`, `OAI.PolycyclicRecognition.controlledGroupCohomologyIso`, `OAI.PolycyclicRecognition.controlledGroupRingValue`, `OAI.PolycyclicRecognition.controlledLinearExtensionMap`, `OAI.PolycyclicRecognition.controlledMetricFolnerPairs_of_product_sets`, `OAI.PolycyclicRecognition.controlledStandardCochainIso`, `OAI.PolycyclicRecognition.coordinateChartPoint`, `OAI.PolycyclicRecognition.cyclicAugmentation`, `OAI.PolycyclicRecognition.cyclicAugmentationSequence`, `OAI.PolycyclicRecognition.cyclicInvariantTopHomologyIso`, `OAI.PolycyclicRecognition.cyclicMeanState`, `OAI.PolycyclicRecognition.cyclicQuotientSequence`, `OAI.PolycyclicRecognition.cyclicSeriesSnoc` and 137 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_AbelianSubgroupRank`, `PolycyclicRecognition_Algebra_ApproximateMidpointProper`, `PolycyclicRecognition_Algebra_CentralLayerTensor`, `PolycyclicRecognition_Algebra_CoefficientConnectingNaturality`, `PolycyclicRecognition_Algebra_CofiberConnecting`, `PolycyclicRecognition_Algebra_ComplexDerivationDescent`, `PolycyclicRecognition_Algebra_ControlledGroupRingCoefficients`, `PolycyclicRecognition_Algebra_ControlledPrismEquation`, `PolycyclicRecognition_Algebra_ControlledPrismIdentity`, `PolycyclicRecognition_Algebra_ControlledProductPairs`, `PolycyclicRecognition_Algebra_CouplingTransfer`, `PolycyclicRecognition_Algebra_CyclicQuotientSequence`, `PolycyclicRecognition_Algebra_DynkinTranslations`, `PolycyclicRecognition_Algebra_EnvelopingTruncation`, `PolycyclicRecognition_Algebra_FactorExtensionTopology`, `PolycyclicRecognition_Algebra_FactorSystemSymmetrySubgroup`, `PolycyclicRecognition_Algebra_FilteredNilpotentPerturbation`, `PolycyclicRecognition_Algebra_FiniteFinsuppHom`, `PolycyclicRecognition_Algebra_FiniteIndexTraceRetract`, `PolycyclicRecognition_Algebra_FixedPowerLogarithms`, `PolycyclicRecognition_Algebra_FreeAbelianLogarithm`, `PolycyclicRecognition_Algebra_GeneratorOrbit`, `PolycyclicRecognition_Algebra_GoodFiniteWordVertices`, `PolycyclicRecognition_Algebra_GradedCoordinateLimit`, `PolycyclicRecognition_Algebra_InducedCyclicDifference`, `PolycyclicRecognition_Algebra_InductionAmbientQuotient`, `PolycyclicRecognition_Algebra_InnerBarTranslation`, `PolycyclicRecognition_Algebra_IntegerInducedTranslation`, `PolycyclicRecognition_Algebra_IntegerRegularCoordinates`, `PolycyclicRecognition_Algebra_InvariantFactor`, `PolycyclicRecognition_Algebra_InverseSection`, `PolycyclicRecognition_Algebra_InverseTransferIdentity`, `PolycyclicRecognition_Algebra_LeftInvariantRiemannianDistance`, `PolycyclicRecognition_Algebra_LeftInvariantRiemannianLength`, `PolycyclicRecognition_Algebra_LeftTangentTrivialization`, `PolycyclicRecognition_Algebra_LinearConjugationCentralizer`, `PolycyclicRecognition_Algebra_LocalGeneratorOrbit`, `PolycyclicRecognition_Algebra_LocallyNilpotentTorsion`, `PolycyclicRecognition_Algebra_MidpointGrids`, `PolycyclicRecognition_Algebra_NilpotentSectionRemainder`, `PolycyclicRecognition_Algebra_NilpotentTorsionQuotientEndgame`, `PolycyclicRecognition_Algebra_NilpotentTorsionSubgroup`, `PolycyclicRecognition_Algebra_NormalEigencharacters`, `PolycyclicRecognition_Algebra_NormalizedTupleDomain`, `PolycyclicRecognition_Algebra_PairAction`, `PolycyclicRecognition_Algebra_PairCharts`, `PolycyclicRecognition_Algebra_PairCoupling`, `PolycyclicRecognition_Algebra_PolyZExtension`, `PolycyclicRecognition_Algebra_PolynomialDerivationCoordinates`, `PolycyclicRecognition_Algebra_PullbackInnerProduct`, `PolycyclicRecognition_Algebra_RationalAbelianTorsion`, `PolycyclicRecognition_Algebra_RationalCentralLayers`, `PolycyclicRecognition_Algebra_RationalNilpotentQuotient`, `PolycyclicRecognition_Algebra_RationalNilpotentTorsion`, `PolycyclicRecognition_Algebra_RationalRepresentationFunctor`, `PolycyclicRecognition_Algebra_RepresentationDirectSum`, `PolycyclicRecognition_Algebra_RepresentationSumExact`, `PolycyclicRecognition_Algebra_RiemannianApproximateMidpoints`, `PolycyclicRecognition_Algebra_SequentialModuleTail`, `PolycyclicRecognition_Algebra_SubgroupInductionCoordinates`, `PolycyclicRecognition_Algebra_SwitchParameterPullback`, `PolycyclicRecognition_Algebra_TorsionFreeAbelianRank`, `PolycyclicRecognition_Algebra_TuplePrism`, `PolycyclicRecognition_Algebra_TwistedBilateralDifference`, `PolycyclicRecognition_Algebra_TwistedBilateralSequence`, `PolycyclicRecognition_Algebra_UnitaryQuotientCocycle`, `PolycyclicRecognition_Algebra_UpperCentralLayerMap`, `PolycyclicRecognition_Algebra_VectorSwitchParameters`, `PolycyclicRecognition_Analysis_CoarseEquivalence`, `PolycyclicRecognition_Analysis_CompactGeneratingBalls`, `PolycyclicRecognition_Analysis_CompactPairs`, `PolycyclicRecognition_Analysis_CompactSegmentLimit`, `PolycyclicRecognition_Analysis_CompactWordCost`, `PolycyclicRecognition_Analysis_ControlledChainRepresentation`, `PolycyclicRecognition_Analysis_ControlledFiniteChains`, `PolycyclicRecognition_Analysis_CoordinateChartSampling`, `PolycyclicRecognition_Analysis_CyclicInvariantMean`, `PolycyclicRecognition_Analysis_FiniteKernelCoarseEquivalence`, `PolycyclicRecognition_Analysis_FiniteSupportInterpolation`, `PolycyclicRecognition_Analysis_FlatSwitchSamples`, `PolycyclicRecognition_Analysis_FolnerInvariantMean`, `PolycyclicRecognition_Analysis_HorseshoeCover`, `PolycyclicRecognition_Analysis_IdealSectionBoxCoordinates`, `PolycyclicRecognition_Analysis_IntegralQuotientKernel`, `PolycyclicRecognition_Analysis_InvariantMeanGenerators`, `PolycyclicRecognition_Analysis_InverseCompactControl`, `PolycyclicRecognition_Analysis_LeftInvariantRiemannianMetric`, `PolycyclicRecognition_Analysis_LinearSupportSymmetries`, `PolycyclicRecognition_Analysis_MetricSegmentsFromMidpoints`, `PolycyclicRecognition_Analysis_MidpointStepPaths`, `PolycyclicRecognition_Analysis_PairChartSampling`, `PolycyclicRecognition_Analysis_ProperMetricMidpoints`, `PolycyclicRecognition_Analysis_RescaledBasisScaleChange`, `PolycyclicRecognition_Analysis_RightFolnerExpansion`, `PolycyclicRecognition_Analysis_SmallCoefficientMean`, `PolycyclicRecognition_Analysis_SmallCoefficientRationalMean`, `PolycyclicRecognition_Analysis_StationaryCentered`, `PolycyclicRecognition_Analysis_StationarySlope`, `PolycyclicRecognition_Analysis_TupleChainPrism`, `PolycyclicRecognition_Analysis_WordChartLeftShift`, `PolycyclicRecognition_Finiteness_ChosenIntegralResolution`, `PolycyclicRecognition_Finiteness_CoarseGroupRingCohomology`, `PolycyclicRecognition_Finiteness_CoefficientNaturalCohomology`, `PolycyclicRecognition_Finiteness_CofiberCochainSequence`, `PolycyclicRecognition_Finiteness_CofiberCohomology`, `PolycyclicRecognition_Finiteness_CofiberResolution`, `PolycyclicRecognition_Finiteness_CokernelResolution`, `PolycyclicRecognition_Finiteness_ConjugationCochains`, `PolycyclicRecognition_Finiteness_ControlledCochainHomotopy`, `PolycyclicRecognition_Finiteness_ControlledCochainMap`, `PolycyclicRecognition_Finiteness_ControlledGroupCohomology`, `PolycyclicRecognition_Finiteness_CyclicInvariantTopHomology`, `PolycyclicRecognition_Finiteness_CyclicTopHomologyInjection`, `PolycyclicRecognition_Finiteness_FiniteGroupSyzygyScalar`, `PolycyclicRecognition_Finiteness_FiniteResolutionTruncation`, `PolycyclicRecognition_Finiteness_FiniteSumCompleteVanishing`, `PolycyclicRecognition_Finiteness_FinsuppCohomology`, `PolycyclicRecognition_Finiteness_FinsuppCompleteVanishing`, `PolycyclicRecognition_Finiteness_FreeAbelianDuality`, `PolycyclicRecognition_Finiteness_HomogeneousCochainCoordinates`, `PolycyclicRecognition_Finiteness_HomogeneousRepresentationCochains`, `PolycyclicRecognition_Finiteness_InducedCohomologyDifference`, `PolycyclicRecognition_Finiteness_InducedTranslationCochains`, `PolycyclicRecognition_Finiteness_InductionCochains`, `PolycyclicRecognition_Finiteness_InfiniteCyclicResolution`, `PolycyclicRecognition_Finiteness_IntegerExtensionDuality`, `PolycyclicRecognition_Finiteness_IntegerExtensionHomology`, `PolycyclicRecognition_Finiteness_IntegerInducedCochains`, `PolycyclicRecognition_Finiteness_NormalHomologyAction`, `PolycyclicRecognition_Finiteness_NormalizedSyzygyIteration`, `PolycyclicRecognition_Finiteness_ProjectiveResolutionSyzygies`, `PolycyclicRecognition_Finiteness_RationalZeroCoefficientHomology`, `PolycyclicRecognition_Finiteness_RepCochainMaps`, `PolycyclicRecognition_Finiteness_ResolutionCoefficientSequence`, `PolycyclicRecognition_Finiteness_SmallCoefficientRing`, `PolycyclicRecognition_Finiteness_TopHomologyNaturality`, `PolycyclicRecognition_Geometry_AdjointMatrixHeight`, `PolycyclicRecognition_Geometry_CartanSupportLegs`, `PolycyclicRecognition_Geometry_CartanWordBasis`, `PolycyclicRecognition_Geometry_CompactSemidirectModel`, `PolycyclicRecognition_Geometry_ComplexifiedLieAutomorphism`, `PolycyclicRecognition_Geometry_ComplexifiedOperatorExponential`, `PolycyclicRecognition_Geometry_ConstructMinimizingLieMetric`, `PolycyclicRecognition_Geometry_ExponentialQuotientSection`, `PolycyclicRecognition_Geometry_ExponentialTupleCoordinates`, `PolycyclicRecognition_Geometry_FixedVectorLieLogarithm`, `PolycyclicRecognition_Geometry_GradedFlowLimit`, `PolycyclicRecognition_Geometry_HeightConjugationDifferential`, `PolycyclicRecognition_Geometry_IndependentWeightCone`, `PolycyclicRecognition_Geometry_NetSmoothing`, `PolycyclicRecognition_Geometry_NilpotentLinearFlow`, `PolycyclicRecognition_Geometry_NormalizedWeightRays`, `PolycyclicRecognition_Geometry_PairHeightCocycle`, `PolycyclicRecognition_Geometry_RepresentedExponentialDifferential`, `PolycyclicRecognition_Geometry_SemidirectProductTopology`, `PolycyclicRecognition_Geometry_TriangularLocalLogarithm`, `PolycyclicRecognition_Geometry_UnipotentLieLogarithm`, `PolycyclicRecognition_Geometry_WeightChambers`, `PolycyclicRecognition_Geometry_WeightedChainMetric`, `PolycyclicRecognition_Lattices_CartanNilshadow`, `PolycyclicRecognition_Lattices_IntegralLatticePowerIndex`, `PolycyclicRecognition_Lattices_LatticeKernelTail`, `PolycyclicRecognition_Lattices_LatticeNormalFlag`, `PolycyclicRecognition_Lattices_NilshadowWeightAction`, `Thompson_FiniteAverage`, `Thompson_InvariantMean`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D001`, `OAIQ093D002`, `OAIQ093D003`, `OAIQ093D004` and `OAIQ093D005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D014` and `OAIQ093D015`; the statements `OAI.PolycyclicRecognition.CartanWordModel.cartan_normal_occupation_error_tendsto_zero`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_segment_volume_sequence`, `OAI.PolycyclicRecognition.affine_of_horizontal_labels`, `OAI_PolycyclicRecognition_affine_profile_of_segment_inequalities` and `OAI.PolycyclicRecognition.supported_profile_increment_of_flow`; the proof of `OAI.PolycyclicRecognition.supported_profile_increment_of_flow`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D001
import Definitions.Def_OAIQ093D002
import Definitions.Def_OAIQ093D003
import Definitions.Def_OAIQ093D004
import Definitions.Def_OAIQ093D005

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveResolutionSyzygies
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projectivity of the top syzygy

Successive quotient terms of a projective resolution fit into short exact
sequences. Finite projective dimension therefore makes the corresponding
top quotient projective; it remains finitely generated when the old term is.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G] (P : ProjectiveResolution (trivialIntegral G))

def resolutionOpcyclesZeroIso : P.complex.opcycles 0 ≅ trivialIntegral G :=
  (P.complex.opcyclesIsCokernel 1 0 (by simp)).coconePointUniqueUpToIso
    P.isColimitCokernelCofork

theorem resolutionOpcycles_projectiveDimension (n d : ℕ)
    [hdim : HasProjectiveDimensionLE (trivialIntegral G) (n + d)] :
    HasProjectiveDimensionLE (P.complex.opcycles n) d := by
  induction n generalizing d with
  | zero =>
    have : HasProjectiveDimensionLT (trivialIntegral G) (d + 1) := by
      simpa only [Nat.zero_add] using hdim
    exact hasProjectiveDimensionLT_of_iso (resolutionOpcyclesZeroIso P).symm (d + 1)
  | succ n ih =>
    have : HasProjectiveDimensionLE (trivialIntegral G) (n + (d + 1)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hdim
    have hq := ih (d + 1)
    exact (resolutionOpcyclesSequence_shortExact P n).hasProjectiveDimensionLT_X₁ (d + 1)
      (hasProjectiveDimensionLT_of_ge (P.complex.X n) 1 (d + 1) (by omega)) hq

theorem resolutionOpcycles_projective (d : ℕ)
    [hdim : HasProjectiveDimensionLE (trivialIntegral G) d] : Projective (P.complex.opcycles d) := by
  have : HasProjectiveDimensionLE (trivialIntegral G) (d + 0) := by simpa using hdim
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mpr
    (resolutionOpcycles_projectiveDimension P d 0)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteResolutionTruncation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.RationalResolution.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite resolution from finite dimension and finite generation

Canonical truncation replaces the last term by its quotient syzygy. The
projectivity of that syzygy follows from finite projective dimension, while
finite generation passes to the quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits

variable {G : Type} [Group G] (P : ProjectiveResolution (trivialIntegral G)) (d : ℕ)

def finiteTruncation : ChainComplex (Rep ℤ G) ℕ :=
  P.complex.truncGE (finiteResolutionEmbedding d)

theorem finiteTruncation_isZero (i : ℕ) (hi : d < i) :
    IsZero ((finiteTruncation P d).X i) := by
  apply P.complex.truncGE (finiteResolutionEmbedding d) |>.isZero_X_of_isStrictlySupported
    (finiteResolutionEmbedding d) i
  intro j hj
  change j.val = i at hj
  omega

def finiteTruncationIso (i : ℕ) (hi : i < d) :
    (finiteTruncation P d).X i ≅ P.complex.X i :=
  P.complex.truncGEXIso (finiteResolutionEmbedding d) (i := ⟨i, by omega⟩) rfl
    (by rw [finiteResolutionEmbedding_boundary]; change i ≠ d; omega)

def finiteTruncationTopIso :
    (finiteTruncation P d).X d ≅ P.complex.opcycles d :=
  P.complex.truncGEXIsoOpcycles (finiteResolutionEmbedding d)
    (i := ⟨d, by omega⟩) rfl ((finiteResolutionEmbedding_boundary d _).mpr rfl)

theorem finiteTruncation_projective
    [HasProjectiveDimensionLE (trivialIntegral G) d] (i : ℕ) :
    Projective ((finiteTruncation P d).X i) := by
  rcases lt_trichotomy i d with hi | hi | hi
  · exact Projective.of_iso (finiteTruncationIso P d i hi).symm inferInstance
  · subst i
    exact Projective.of_iso (finiteTruncationTopIso P d).symm
      (resolutionOpcycles_projective P d)
  · exact (finiteTruncation_isZero P d i hi).projective

instance finiteResolution_single_supported :
    ((ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G)).IsStrictlySupported
      (finiteResolutionEmbedding d) where
  isZero i hi := by
    apply HomologicalComplex.isZero_single_obj_X
    intro h
    subst i
    exact hi ⟨0, by omega⟩ rfl

def finiteTruncationAugmentation :
    finiteTruncation P d ⟶ (ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G) :=
  HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d) ≫
    inv (((ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G)).πTruncGE
      (finiteResolutionEmbedding d))

instance finiteTruncationAugmentation_quasiIso :
    QuasiIso (finiteTruncationAugmentation P d) := by
  have : QuasiIso (HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d)) :=
    (HomologicalComplex.quasiIso_truncGEMap_iff P.π (finiteResolutionEmbedding d)).mpr
      (fun _ _ _ => inferInstance)
  exact quasiIso_comp (HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d))
    (inv (((ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G)).πTruncGE
      (finiteResolutionEmbedding d)))

def finiteProjectiveResolution [HasProjectiveDimensionLE (trivialIntegral G) d] :
    ProjectiveResolution (trivialIntegral G) where
  complex := finiteTruncation P d
  projective := finiteTruncation_projective P d
  π := finiteTruncationAugmentation P d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InfiniteCyclicResolution
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite free resolution for an infinite cyclic group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped MonoidAlgebra

-- Use the scalar structure stored in a representation, including for integer scalars.
attribute [local instance 2000] Rep.hV2

variable (G : Type) [CommGroup G]

def cyclicAugmentation : Rep.leftRegular ℤ G ⟶ trivialIntegral G :=
  Rep.leftRegularHom _ 1

theorem cyclicDifference_augmentation (g : G) :
    cyclicDifference G g ≫ cyclicAugmentation G = 0 := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro x
  change integralAugmentation G (Representation.leftRegular ℤ G g x - x) = 0
  rw [map_sub, integralAugmentation_leftRegular, sub_self]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CyclicQuotientSequence
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient sequence for an infinite cyclic quotient

Inflating the cyclic augmentation sequence gives the two copies of the
quotient permutation module used in the cyclic-extension argument.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (Q : Type) [CommGroup Q]

def cyclicAugmentationSequence (z : Q) : ShortComplex (Rep ℤ Q) :=
  ShortComplex.mk (cyclicDifference Q z) (cyclicAugmentation Q)
    (cyclicDifference_augmentation Q z)

theorem cyclicAugmentationSequence_exact (z : Q)
    (hz : ∀ x, x ∈ Subgroup.zpowers z) : (cyclicAugmentationSequence Q z).Exact := by
  apply (forget₂ (Rep ℤ Q) (ModuleCat ℤ)).reflects_exact_of_faithful
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (Representation.leftRegular ℤ Q z - LinearMap.id) =
    LinearMap.ker (integralAugmentation Q)
  exact (integralAugmentation_ker_of_cyclic Q z hz).symm

theorem cyclicAugmentationSequence_shortExact [Infinite Q] (z : Q)
    (hz : ∀ x, x ∈ Subgroup.zpowers z) : (cyclicAugmentationSequence Q z).ShortExact where
  exact := cyclicAugmentationSequence_exact Q z hz
  mono_f := by
    rw [Rep.mono_iff_injective]
    exact leftRegular_difference_injective z hz
  epi_g := by
    rw [Rep.epi_iff_surjective]
    intro r
    refine ⟨MonoidAlgebra.single 1 r, ?_⟩
    exact integralAugmentation_single Q 1 r

variable {G : Type} [Group G]

def cyclicQuotientSequence (q : G →* Q) (z : Q) : ShortComplex (Rep ℤ G) :=
  (cyclicAugmentationSequence Q z).map (Rep.resFunctor q)

theorem cyclicQuotientSequence_shortExact [Infinite Q] (q : G →* Q) (z : Q)
    (hz : ∀ x, x ∈ Subgroup.zpowers z) : (cyclicQuotientSequence Q q z).ShortExact :=
  (Rep.shortExact_res q).mpr (cyclicAugmentationSequence_shortExact Q z hz)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CofiberResolution
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exactness of the cone on an injective map of resolved representations -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]
  {A B : Rep k G} (P : ProjectiveResolution A) (Q : ProjectiveResolution B)
  (φ : P.complex ⟶ Q.complex)

theorem repCofiber_boundary_of_lift_fst (i : ℕ)
    (x : (repCofiber φ).X (i + 1))
    (hx : ((repCofiber φ).d (i + 1) i).hom x = 0)
    (a : P.complex.X (i + 1))
    (ha : (P.complex.d (i + 1) i).hom a = (repCofiberFst φ i).hom x) :
    ∃ y : (repCofiber φ).X (i + 2),
      ((repCofiber φ).d (i + 2) (i + 1)).hom y = x := by
  have hsum := repCofiber_snd_d φ i x
  rw [hx, map_zero] at hsum
  have hcycle : (Q.complex.d (i + 1) i).hom
      ((repCofiberSnd φ (i + 1)).hom x + (φ.f (i + 1)).hom a) = 0 := by
    have hc := congrArg (fun f => f.hom a) (φ.comm (i + 1) i)
    change (Q.complex.d (i + 1) i).hom ((φ.f (i + 1)).hom a) =
      (φ.f i).hom ((P.complex.d (i + 1) i).hom a) at hc
    simp only [map_add]
    rw [hc, ha]
    exact (add_comm _ _).trans hsum.symm
  obtain ⟨b, hb⟩ := (rep_shortComplex_exact_iff _).mp (Q.exact_succ i) _ hcycle
  let y := (repCofiberInl φ (i + 1)).hom (-a) +
    (repCofiberInr φ (i + 2)).hom b
  refine ⟨y, repCofiber_ext φ i ?_ ?_⟩
  · rw [repCofiber_fst_d]
    simp only [y, map_add, repCofiber_fst_inl, repCofiber_fst_inr, add_zero,
      map_neg, ha, neg_neg]
  · rw [repCofiber_snd_d]
    simp only [y, map_add, repCofiber_fst_inl, repCofiber_fst_inr,
      repCofiber_snd_inl, repCofiber_snd_inr, add_zero, map_neg, map_zero]
    rw [hb]
    abel

theorem repCofiber_boundary_of_mono (f : A ⟶ B) [Mono f]
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) (i : ℕ)
    (x : (repCofiber φ).X (i + 1))
    (hx : ((repCofiber φ).d (i + 1) i).hom x = 0) :
    ∃ y : (repCofiber φ).X (i + 2),
      ((repCofiber φ).d (i + 2) (i + 1)).hom y = x := by
  have ha : ∃ a : P.complex.X (i + 1),
      (P.complex.d (i + 1) i).hom a = (repCofiberFst φ i).hom x := by
    cases i with
    | zero =>
        have hsum := repCofiber_snd_d φ 0 x
        rw [hx, map_zero] at hsum
        have hzero : (P.π.f 0).hom ((repCofiberFst φ 0).hom x) = 0 := by
          apply ((Rep.mono_iff_injective f).mp inferInstance)
          erw [map_zero]
          have hc := congrArg (fun u => u.hom ((repCofiberFst φ 0).hom x)) hφ
          change (Q.π.f 0).hom ((φ.f 0).hom ((repCofiberFst φ 0).hom x)) =
            f.hom ((P.π.f 0).hom ((repCofiberFst φ 0).hom x)) at hc
          have hd := congrArg (fun u => u.hom ((repCofiberSnd φ 1).hom x))
            Q.complex_d_comp_π_f_zero
          change (Q.π.f 0).hom ((Q.complex.d 1 0).hom
            ((repCofiberSnd φ 1).hom x)) = 0 at hd
          rw [← hc]
          have hz := congrArg (Q.π.f 0).hom hsum.symm
          simpa only [map_add, hd, add_zero, map_zero] using! hz
        exact (rep_shortComplex_exact_iff _).mp P.exact₀ _ hzero
    | succ i =>
        have hz := repCofiber_fst_d φ i x
        rw [hx, map_zero] at hz
        have hzero := neg_eq_zero.mp hz.symm
        exact (rep_shortComplex_exact_iff _).mp (P.exact_succ i) _ hzero
  obtain ⟨a, ha⟩ := ha
  exact repCofiber_boundary_of_lift_fst P Q φ i x hx a ha

theorem repCofiber_exactAt_of_mono (f : A ⟶ B) [Mono f]
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) (i : ℕ) :
    (repCofiber φ).ExactAt (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp)]
  exact (rep_shortComplex_exact_iff _).mpr
    (repCofiber_boundary_of_mono P Q φ f hφ i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CokernelResolution
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite projective resolution for the cokernel in the cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (S : ShortComplex (Rep ℤ G))
  (P : ProjectiveResolution S.X₁) (Q : ProjectiveResolution S.X₂)

theorem cokernelResolutionAugmentation_boundary (hS : S.ShortExact)
    (x : (repCofiber (cokernelResolutionMap S P Q)).X 0)
    (hx : ((cokernelResolutionAugmentation S P Q).f 0).hom x = 0) :
    ∃ y : (repCofiber (cokernelResolutionMap S P Q)).X 1,
      ((repCofiber (cokernelResolutionMap S P Q)).d 1 0).hom y = x := by
  let φ := cokernelResolutionMap S P Q
  rw [cokernelResolutionAugmentation_apply] at hx
  obtain ⟨a, ha⟩ := (rep_shortComplex_exact_iff S).mp hS.exact _ hx
  obtain ⟨a₀, ha₀⟩ := ((Rep.epi_iff_surjective (P.π.f 0)).mp inferInstance) a
  have hc := congrArg (fun f => f.hom a₀) (ProjectiveResolution.lift_commutes_zero S.f P Q)
  change (Q.π.f 0).hom ((φ.f 0).hom a₀) = S.f.hom ((P.π.f 0).hom a₀) at hc
  have hz : (Q.π.f 0).hom
      ((repCofiberSnd φ 0).hom x - (φ.f 0).hom a₀) = 0 := by
    rw [map_sub, hc, ha₀, ha, sub_self]
  obtain ⟨b, hb⟩ := (rep_shortComplex_exact_iff _).mp Q.exact₀ _ hz
  let y := (repCofiberInl φ 0).hom a₀ + (repCofiberInr φ 1).hom b
  refine ⟨y, repCofiber_ext_zero φ ?_⟩
  rw [repCofiber_snd_d]
  simp only [y, map_add, repCofiber_fst_inl, repCofiber_fst_inr,
    repCofiber_snd_inl, repCofiber_snd_inr, add_zero, zero_add]
  rw [hb]
  abel

theorem cokernelResolutionAugmentation_quasiIso (hS : S.ShortExact) :
    QuasiIso (cokernelResolutionAugmentation S P Q) where
  quasiIsoAt i := by
    cases i with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff,
          ShortComplex.quasiIso_iff_of_zeros' _ (by simp; rfl) rfl rfl]
        constructor
        · exact (rep_shortComplex_exact_iff _).mpr
            (cokernelResolutionAugmentation_boundary S P Q hS)
        · rw [Rep.epi_iff_surjective]
          exact cokernelResolutionAugmentation_surjective S P Q hS
    | succ i =>
        rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
        let := hS.mono_f
        exact repCofiber_exactAt_of_mono P Q (cokernelResolutionMap S P Q) S.f
          (ProjectiveResolution.lift_commutes_zero S.f P Q) i

def cokernelProjectiveResolution (hS : S.ShortExact) : ProjectiveResolution S.X₃ where
  complex := repCofiber (cokernelResolutionMap S P Q)
  π := cokernelResolutionAugmentation S P Q
  quasiIso := cokernelResolutionAugmentation_quasiIso S P Q hS

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TwistedBilateralDifference
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the coefficient twist from a bilateral shift -/

noncomputable section
namespace PolycyclicRecognition

open Representation
variable (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M]

def twistedBilateralSum (e : M ≃ₗ[k] M) : (ℤ →₀ M) →ₗ[k] M :=
  (bilateralSum k M).comp (bilateralGauge k M e).toLinearMap

theorem twistedBilateralDifference_injective (e : M ≃ₗ[k] M) :
    Function.Injective (twistedBilateralDifference k M e) := by
  intro f g h
  apply (bilateralGauge k M e).injective
  apply bilateralDifference_injective k M
  simpa only [bilateralGauge_difference] using congrArg (bilateralGauge k M e) h

theorem twistedBilateralSum_surjective (e : M ≃ₗ[k] M) :
    Function.Surjective (twistedBilateralSum k M e) :=
  (bilateralSum_surjective k M).comp (bilateralGauge k M e).surjective

theorem twistedBilateralSum_ker_eq_range (e : M ≃ₗ[k] M) :
    LinearMap.ker (twistedBilateralSum k M e) =
      LinearMap.range (twistedBilateralDifference k M e) := by
  ext f
  change bilateralSum k M (bilateralGauge k M e f) = 0 ↔ _
  rw [← LinearMap.mem_ker, bilateralSum_ker_eq_range]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(bilateralGauge k M e).symm g, ?_⟩
    apply (bilateralGauge k M e).injective
    rw [bilateralGauge_difference, LinearEquiv.apply_symm_apply, hg]
  · rintro ⟨g, rfl⟩
    exact ⟨bilateralGauge k M e g, (bilateralGauge_difference k M e g).symm⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TwistedBilateralSequence
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exactness and cokernel of the twisted bilateral difference -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

variable (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M]

theorem twistedBilateralDifference_sum (e : M ≃ₗ[k] M) (f : ℤ →₀ M) :
    twistedBilateralSum k M e (twistedBilateralDifference k M e f) = 0 := by
  have hm : twistedBilateralDifference k M e f ∈
      LinearMap.range (twistedBilateralDifference k M e) := ⟨f, rfl⟩
  rw [← twistedBilateralSum_ker_eq_range] at hm
  exact hm

def twistedBilateralSequence (e : M ≃ₗ[k] M) : ShortComplex (ModuleCat k) :=
  ShortComplex.mk (ModuleCat.ofHom (twistedBilateralDifference k M e))
    (ModuleCat.ofHom (twistedBilateralSum k M e)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact twistedBilateralDifference_sum k M e f)

theorem twistedBilateralSequence_shortExact (e : M ≃ₗ[k] M) :
    (twistedBilateralSequence k M e).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (twistedBilateralSum_ker_eq_range k M e).symm
  mono_f := (ModuleCat.mono_iff_injective _).mpr (twistedBilateralDifference_injective k M e)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (twistedBilateralSum_surjective k M e)

def twistedBilateralCokernelIso (e : M ≃ₗ[k] M) :
    cokernel (ModuleCat.ofHom (twistedBilateralDifference k M e)) ≅ ModuleCat.of k M :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (twistedBilateralSequence_shortExact k M e).gIsCokernel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteFinsuppHom
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Hom out of a finite group-ring module commutes with direct sums -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] (G : Type) [Group G]
  (α : Type) (A B : Rep k G)

def finiteFinsuppHomEquiv [Module.Finite k[G] A.ρ.asModule] :
    (α →₀ (A ⟶ B)) ≃ₗ[k] (A ⟶ Rep.finsupp α B) :=
  (Finsupp.mapRange.linearEquiv (representationModuleHomEquiv k G A B)).trans
    ((LinearEquiv.ofBijective (LinearMap.finsuppLinearMap k)
      (LinearMap.finsuppLinearMap_bijective_of_moduleFinite (R := k[G])
        (M := A.ρ.asModule) (N := B.ρ.asModule) (ι := α) (S := k))).trans
      ((finsuppHomPostcompEquiv k G α A B).trans
        (representationModuleHomEquiv k G A (Rep.finsupp α B)).symm))

@[simp] theorem finiteFinsuppHomEquiv_apply [Module.Finite k[G] A.ρ.asModule]
    (x : α →₀ (A ⟶ B)) (a : A) (i : α) :
    ((finiteFinsuppHomEquiv k G α A B x).hom a) i = (x i).hom a := by
  change (((LinearMap.finsuppLinearMap k)
    (Finsupp.mapRange.linearEquiv (representationModuleHomEquiv k G A B) x))
      (A.ρ.asModuleEquiv.symm a)) i = (x i).hom a
  rw [LinearMap.finsuppLinearMap_apply_apply_apply]
  rfl

@[simp] theorem finiteFinsuppHomEquiv_single [Module.Finite k[G] A.ρ.asModule]
    (i : α) (f : A ⟶ B) (a : A) :
    (finiteFinsuppHomEquiv k G α A B (Finsupp.single i f)).hom a =
      Finsupp.single i (f.hom a) := by
  ext j
  rw [finiteFinsuppHomEquiv_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [h]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IntegerRegularCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regular module in coordinates adapted to a cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)

theorem integerRegularLinearEquiv_lift_action (x : k[G]) :
    integerRegularLinearEquiv k q t ht (Representation.leftRegular k G t x) =
      Finsupp.mapRange.linearMap (kernelConjugationLinearEquiv k q t).toLinearMap
        (bilateralTranslation k k[q.ker] (Multiplicative.ofAdd 1)
          (integerRegularLinearEquiv k q t ht x)) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g a =>
      have hh : integerQuotientHeight q t = 1 := by simp [integerQuotientHeight, ht]
      simp [integerQuotientPart_lift_mul, kernelConjugationLinearEquiv, hh]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RepCochainMaps
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maps and homotopies on cochains computed from representation complexes -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] {G : Type} [Group G]
  {P Q R : ChainComplex (Rep k G) ℕ}

@[simp] theorem repCochainPostcomp_apply {A B : Rep k G} (u : A ⟶ B)
    (i : ℕ) (f : P.X i ⟶ A) :
    ((repCochainPostcomp k P u).f i).hom f = f ≫ u := rfl

def repCochainPostcompIso (P : ChainComplex (Rep k G) ℕ) {A B : Rep k G} (e : A ≅ B) :
    P.linearYonedaObj k A ≅ P.linearYonedaObj k B where
  hom := repCochainPostcomp k P e.hom
  inv := repCochainPostcomp k P e.inv
  hom_inv_id := by
    ext i f
    change P.X i ⟶ A at f
    change (f ≫ e.hom) ≫ e.inv = f
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    ext i f
    change P.X i ⟶ B at f
    change (f ≫ e.inv) ≫ e.hom = f
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ConjugationCochains
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The automorphism of kernel cohomology induced by conjugation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] {H : Type} [Group H]

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def conjugationCoefficientCochainsIso (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) :
    P.complex.linearYonedaObj k (Rep.leftRegular k N) ≅
      (conjugatedResolution k N t P).complex.linearYonedaObj k (Rep.leftRegular k N) :=
  restrictionCochainsIso k (MulAut.conjNormal (H := N) t⁻¹) P.complex _ ≪≫
    repCochainPostcompIso k _
      (regularRestrictionIso k (MulAut.conjNormal (H := N) t⁻¹))

def conjugationCochainEquiv (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) :
    HomotopyEquiv (P.complex.linearYonedaObj k (Rep.leftRegular k N))
      (P.complex.linearYonedaObj k (Rep.leftRegular k N)) :=
  (HomotopyEquiv.ofIso (conjugationCoefficientCochainsIso k N t P)).trans
    (repCochainHomotopyEquiv k
      (ProjectiveResolution.homotopyEquiv P (conjugatedResolution k N t P)) _)

def conjugationCohomologyIso (t : G) (P : ProjectiveResolution (Rep.trivial k N k)) (i : ℕ) :
    (P.complex.linearYonedaObj k (Rep.leftRegular k N)).homology i ≅
      (P.complex.linearYonedaObj k (Rep.leftRegular k N)).homology i :=
  (conjugationCochainEquiv k N t P).toHomologyIso i

theorem conjugationCochainEquiv_apply (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) (i : ℕ)
    (f : P.complex.X i ⟶ Rep.leftRegular k N) (a : P.complex.X i) :
    ((((conjugationCochainEquiv k N t P).hom.f i).hom f).hom a) =
      (MonoidAlgebra.domCongr k k (MulAut.conjNormal (H := N) t⁻¹).symm)
        (f.hom (((conjugationResolutionLift k N t P).f i).hom a)) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InductionCochains
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frobenius reciprocity for the induced resolution's cochains -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalInductionCochainsIso (P : ProjectiveResolution (Rep.trivial ℤ N ℤ))
    (A : Rep ℤ G) :
    (normalInducedResolution ℤ N P).complex.linearYonedaObj ℤ A ≅
      P.complex.linearYonedaObj ℤ (Rep.res N.subtype A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (Rep.indResHomEquiv N.subtype (P.complex.X i) A).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change P.complex.d j i ≫ Rep.indResHomEquiv N.subtype (P.complex.X i) A f =
        Rep.indResHomEquiv N.subtype (P.complex.X j) A (Rep.indMap N.subtype (P.complex.d j i) ≫ f)
      exact ((Rep.indResAdjunction ℤ N.subtype).homEquiv_naturality_left (P.complex.d j i) f).symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InducedTranslationCochains
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frobenius reciprocity and the chain-level quotient translation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

theorem inducedSemilinearMap_frobenius (t : G) (A B : Rep k N) (C : Rep k G)
    (b : A ⟶ Rep.res (MulAut.conjNormal (H := N) t⁻¹).toMonoidHom B)
    (f : Rep.ind N.subtype B ⟶ C) (a : A) :
    (Rep.indResHomEquiv N.subtype A C (inducedSemilinearMap k N t A B b ≫ f)).hom a =
      C.ρ t ((Rep.indResHomEquiv N.subtype B C f).hom (b.hom a)) := by
  change f.hom ((inducedSemilinearMap k N t A B b).hom (IndV.mk N.subtype A.ρ 1 a)) =
    C.ρ t (f.hom (IndV.mk N.subtype B.ρ 1 (b.hom a)))
  rw [inducedSemilinearMap_mk, mul_one]
  have h := Rep.hom_comm_apply f t (IndV.mk N.subtype B.ρ 1 (b.hom a))
  simpa only [Rep.ind, Representation.ind_mk, one_mul] using h

theorem inducedTranslation_frobenius (t : G)
    (P : ProjectiveResolution (Rep.trivial k N k)) (C : Rep k G) (i : ℕ)
    (f : Rep.ind N.subtype (P.complex.X i) ⟶ C) (a : P.complex.X i) :
    (Rep.indResHomEquiv N.subtype (P.complex.X i) C
      ((inducedTranslation k N t P).f i ≫ f)).hom a =
        C.ρ t ((Rep.indResHomEquiv N.subtype (P.complex.X i) C f).hom
          (((conjugationResolutionLift k N t P).f i).hom a)) :=
  inducedSemilinearMap_frobenius k N t _ _ C _ f a

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IntegerInducedTranslation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The induced translation is a shift with a cochain conjugation twist -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)

def integerInducedHomEquiv (A : Rep k q.ker) [Module.Finite k[q.ker] A.ρ.asModule] :
    (Rep.ind q.ker.subtype A ⟶ Rep.leftRegular k G) ≃ₗ[k]
      (ℤ →₀ (A ⟶ Rep.leftRegular k q.ker)) :=
  (Rep.indResHomEquiv q.ker.subtype A (Rep.leftRegular k G)).trans
    ((Linear.homCongr k (Iso.refl A) (integerRestrictedRegularIso k q t ht)).trans
      (finiteFinsuppHomEquiv k q.ker ℤ A (Rep.leftRegular k q.ker)).symm)

theorem integerInducedHomEquiv_pointwise (A : Rep k q.ker)
    [Module.Finite k[q.ker] A.ρ.asModule]
    (f : Rep.ind q.ker.subtype A ⟶ Rep.leftRegular k G) (a : A) :
    (finiteFinsuppHomEquiv k q.ker ℤ A (Rep.leftRegular k q.ker)
      (integerInducedHomEquiv k q t ht A f)).hom a =
        integerRegularLinearEquiv k q t ht
          ((Rep.indResHomEquiv q.ker.subtype A (Rep.leftRegular k G) f).hom a) := by
  simp only [integerInducedHomEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem integerInducedHomEquiv_apply (A : Rep k q.ker)
    [Module.Finite k[q.ker] A.ρ.asModule]
    (f : Rep.ind q.ker.subtype A ⟶ Rep.leftRegular k G) (a : A) (j : ℤ) :
    ((integerInducedHomEquiv k q t ht A f) j).hom a =
      integerRegularLinearEquiv k q t ht
        ((Rep.indResHomEquiv q.ker.subtype A (Rep.leftRegular k G) f).hom a) j := by
  rw [← finiteFinsuppHomEquiv_apply, integerInducedHomEquiv_pointwise]

theorem integerInducedHomEquiv_translation
    (P : ProjectiveResolution (Rep.trivial k q.ker k)) (i : ℕ)
    [Module.Finite k[q.ker] (P.complex.X i).ρ.asModule]
    (f : Rep.ind q.ker.subtype (P.complex.X i) ⟶ Rep.leftRegular k G) :
    integerInducedHomEquiv k q t ht (P.complex.X i)
        ((inducedTranslation k q.ker t P).f i ≫ f) =
      Finsupp.mapRange.linearMap ((conjugationCochainEquiv k q.ker t P).hom.f i).hom
        (bilateralTranslation k (P.complex.X i ⟶ Rep.leftRegular k q.ker)
          (Multiplicative.ofAdd 1) (integerInducedHomEquiv k q t ht (P.complex.X i) f)) := by
  apply Finsupp.ext
  intro j
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  change ((integerInducedHomEquiv k q t ht (P.complex.X i)
      ((inducedTranslation k q.ker t P).f i ≫ f)) j).hom a = _
  rw [integerInducedHomEquiv_apply, inducedTranslation_frobenius,
    integerRegularLinearEquiv_lift_action]
  change kernelConjugationLinearEquiv k q t
      (integerRegularLinearEquiv k q t ht
        ((Rep.indResHomEquiv q.ker.subtype (P.complex.X i) (Rep.leftRegular k G) f).hom
          (((conjugationResolutionLift k q.ker t P).f i).hom a)) (-1 + j)) =
    ((((conjugationCochainEquiv k q.ker t P).hom.f i).hom
      ((integerInducedHomEquiv k q t ht (P.complex.X i) f) (-1 + j))).hom a)
  rw [conjugationCochainEquiv_apply, inverse_conjugation_eq]
  exact congrArg (kernelConjugationLinearEquiv k q t)
    (integerInducedHomEquiv_apply k q t ht (P.complex.X i) f
      (((conjugationResolutionLift k q.ker t P).f i).hom a) (-1 + j)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FinsuppCohomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct sums in cohomology computed from finite group-ring resolutions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] (G : Type) [Group G] (α : Type)

theorem finiteFinsuppHomEquiv_precomp {A B C : Rep k G}
    [Module.Finite k[G] A.ρ.asModule] [Module.Finite k[G] B.ρ.asModule]
    (u : A ⟶ B) (x : α →₀ (B ⟶ C)) :
    finiteFinsuppHomEquiv k G α A C
        (Finsupp.mapRange.linearMap (Linear.leftComp k C u) x) =
      u ≫ finiteFinsuppHomEquiv k G α B C x := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro a
  apply Finsupp.ext
  intro i
  change ((finiteFinsuppHomEquiv k G α A C _).hom a) i =
    ((finiteFinsuppHomEquiv k G α B C x).hom (u.hom a)) i
  rw [finiteFinsuppHomEquiv_apply, finiteFinsuppHomEquiv_apply]
  rfl

def finsuppCochainsIso (P : ProjectiveResolution (Rep.trivial k G k))
    (hP : ∀ i, Module.Finite k[G] (P.complex.X i).ρ.asModule) (A : Rep k G) :
    ((moduleFinsuppFunctor k α).mapHomologicalComplex _).obj
        (P.complex.linearYonedaObj k A) ≅
      P.complex.linearYonedaObj k (Rep.finsupp α A) := by
  letI (i : ℕ) : Module.Finite k[G] (P.complex.X i).ρ.asModule := hP i
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (finiteFinsuppHomEquiv k G α (P.complex.X i) A).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change P.complex.d j i ≫ finiteFinsuppHomEquiv k G α (P.complex.X i) A x =
    finiteFinsuppHomEquiv k G α (P.complex.X j) A
      (Finsupp.mapRange.linearMap (Linear.leftComp k A (P.complex.d j i)) x)
  exact (finiteFinsuppHomEquiv_precomp k G α (P.complex.d j i) x).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegerInducedCochains
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer coordinates on the induced resolution and its cohomology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)
  (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))
  (hP : ∀ i, Module.Finite ℤ[q.ker] (P.complex.X i).ρ.asModule)

def integerInducedCochainsIso :
    (normalInducedResolution ℤ q.ker P).complex.linearYonedaObj ℤ (Rep.leftRegular ℤ G) ≅
      ((moduleFinsuppFunctor ℤ ℤ).mapHomologicalComplex _).obj
        (P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)) :=
  normalInductionCochainsIso q.ker P _ ≪≫
    repCochainPostcompIso ℤ P.complex (integerRestrictedRegularIso ℤ q t ht) ≪≫
      (finsuppCochainsIso ℤ q.ker ℤ P hP (Rep.leftRegular ℤ q.ker)).symm

theorem integerInducedCochainsIso_translation :
    repCochainPrecomp ℤ (inducedTranslation ℤ q.ker t P) (Rep.leftRegular ℤ G) ≫
        (integerInducedCochainsIso q t ht P hP).hom =
      (integerInducedCochainsIso q t ht P hP).hom ≫
        bilateralCochainTwist ℤ (P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker))
          (conjugationCochainEquiv ℤ q.ker t P).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  let := hP i
  change integerInducedHomEquiv ℤ q t ht (P.complex.X i)
      ((inducedTranslation ℤ q.ker t P).f i ≫ f) =
    Finsupp.mapRange.linearMap ((conjugationCochainEquiv ℤ q.ker t P).hom.f i).hom
      (bilateralTranslation ℤ (P.complex.X i ⟶ Rep.leftRegular ℤ q.ker)
        (Multiplicative.ofAdd 1) (integerInducedHomEquiv ℤ q t ht (P.complex.X i) f))
  exact integerInducedHomEquiv_translation ℤ q t ht P i f

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InducedCohomologyDifference
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injectivity and cokernel of translation minus identity on induced cohomology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] Finsupp.module

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)
  (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))
  (hP : ∀ i, Module.Finite ℤ[q.ker] (P.complex.X i).ρ.asModule)

def inducedTranslationDifference := inducedTranslation ℤ q.ker t P - 𝟙 _

def inducedCohomologyDifference (i : ℕ) :=
  HomologicalComplex.homologyMap
    (repCochainPrecomp ℤ (inducedTranslationDifference q t P) (Rep.leftRegular ℤ G)) i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InducedCyclicDifference
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit translation difference lifts the cyclic augmentation map -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)]

attribute [local instance] OAI.PolycyclicRecognition.instCommGroupQuotientSubgroup_solutions
def inducedCyclicDifferenceHomotopy (t : G) (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) :
    Homotopy
      (ProjectiveResolution.lift
        (Rep.resMap (QuotientGroup.mk' N) (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t)))
        (quotientInducedResolution N P) (quotientInducedResolution N P))
      (inducedTranslation ℤ N t P - 𝟙 _) := by
  let R := quotientInducedResolution N P
  let f := Rep.resMap (QuotientGroup.mk' N)
    (cyclicDifference (G ⧸ N) (QuotientGroup.mk' N t))
  let u : ProjectiveResolution.Hom R R f :=
    ⟨inducedTranslation ℤ N t P - 𝟙 _, inducedDifference_augmentation N t P⟩
  exact ProjectiveResolution.liftHomotopy f _ _ (ProjectiveResolution.lift_commutes f R R)
    u.hom_comp_π

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CofiberCochainSequence
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The short exact sequence of cochains of a mapping cone -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {k G : Type} [CommRing k] [Group G]
  {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q) (A : Rep k G)

def cofiberCochainProjection :
    ChainComplex.linearYonedaObj (repCofiber φ) k A ⟶ Q.linearYonedaObj k A :=
  repCochainPrecomp k (homotopyCofiber.inr φ) A

theorem cofiberCochainInclusion_projection :
    cofiberCochainInclusion φ A ≫ cofiberCochainProjection φ A = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero => exact zero_comp
  | succ i =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let f : P.X i ⟶ A := (cochainSuccessorXIso (P.linearYonedaObj k A) i).hom.hom x
    change repCofiberInr φ (i + 1) ≫
        (repCofiberFst φ i ≫ f) = 0
    rw [← Category.assoc, homotopyCofiber.inrX_fstX φ (i + 1) i rfl, zero_comp]

def cofiberCochainSequence : ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  ShortComplex.mk (cofiberCochainInclusion φ A) (cofiberCochainProjection φ A)
    (cofiberCochainInclusion_projection φ A)

theorem cofiberCochainProjection_surjective (i : ℕ) :
    Function.Surjective ((cofiberCochainProjection φ A).f i).hom := by
  intro f
  change Q.X i ⟶ A at f
  refine ⟨repCofiberSnd φ i ≫ f, ?_⟩
  change repCofiberInr φ i ≫ (repCofiberSnd φ i ≫ f) = f
  rw [← Category.assoc, homotopyCofiber.inrX_sndX, Category.id_comp]

theorem cofiberCochainSequence_exact_degree (i : ℕ) :
    ((cofiberCochainSequence φ A).map (eval _ _ i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((repCofiber φ).X i ⟶ A) at f
  change repCofiberInr φ i ≫ f = 0 at hf
  cases i with
  | zero =>
    refine ⟨0, ?_⟩
    change 0 = f
    calc
      0 = repCofiberSnd φ 0 ≫ (repCofiberInr φ 0 ≫ f) := by rw [hf, comp_zero]
      _ = f := by
        rw [← Category.assoc, homotopyCofiber.sndX_inrX φ 0 (by simp)]
        exact Category.id_comp f
  | succ i =>
    let E : (cochainSuccessor (P.linearYonedaObj k A)).X (i + 1) ≃ₗ[k] (P.X i ⟶ A) :=
      (cochainSuccessorXIso (P.linearYonedaObj k A) i).toLinearEquiv
    refine ⟨E.symm (repCofiberInl φ i ≫ f), ?_⟩
    change repCofiberFst φ i ≫ E (E.symm (repCofiberInl φ i ≫ f)) = f
    rw [E.apply_symm_apply]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change f.hom ((repCofiberInl φ i).hom ((repCofiberFst φ i).hom x)) = f.hom x
    have h := congrArg f.hom (repCofiber_decompose φ i x)
    have hz : f.hom ((repCofiberInr φ (i + 1)).hom ((repCofiberSnd φ (i + 1)).hom x)) = 0 :=
      congrArg (fun u => u.hom ((repCofiberSnd φ (i + 1)).hom x)) hf
    simpa only [map_add, hz, add_zero] using h

theorem cofiberCochainSequence_shortExact : (cofiberCochainSequence φ A).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact
    { exact := cofiberCochainSequence_exact_degree φ A i
      mono_f := (ModuleCat.mono_iff_injective _).mpr (cofiberCochainInclusion_injective φ A i)
      epi_g := (ModuleCat.epi_iff_surjective _).mpr (cofiberCochainProjection_surjective φ A i) }

theorem cofiberCochainSection_projection (i : ℕ) :
    cofiberCochainSectionComponent φ A i ≫ (cofiberCochainProjection φ A).f i = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (Q.X i ⟶ A) at f
  change repCofiberInr φ i ≫ (repCofiberSnd φ i ≫ f) = f
  rw [← Category.assoc, homotopyCofiber.inrX_sndX, Category.id_comp]

theorem cofiberCochainSection_d (i : ℕ) :
    cofiberCochainSectionComponent φ A i ≫
        (ChainComplex.linearYonedaObj (repCofiber φ) k A).d i (i + 1) =
      (repCochainPrecomp k φ A).f i ≫
        (cochainSuccessorXIso (P.linearYonedaObj k A) i).inv ≫
          (cofiberCochainInclusion φ A).f (i + 1) +
        (Q.linearYonedaObj k A).d i (i + 1) ≫ cofiberCochainSectionComponent φ A (i + 1) := by
  change _ = (repCochainPrecomp k φ A).f i ≫
      (cochainSuccessorXIso (P.linearYonedaObj k A) i).inv ≫
        ((cochainSuccessorXIso (P.linearYonedaObj k A) i).hom ≫
          ModuleCat.ofHom (Linear.leftComp k A (repCofiberFst φ i))) + _
  erw [Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (Q.X i ⟶ A) at f
  change (repCofiber φ).d (i + 1) i ≫ (repCofiberSnd φ i ≫ f) =
    repCofiberFst φ i ≫ (φ.f i ≫ f) + repCofiberSnd φ (i + 1) ≫ (Q.d (i + 1) i ≫ f)
  have hd : (repCofiber φ).d (i + 1) i ≫ repCofiberSnd φ i =
      repCofiberFst φ i ≫ φ.f i + repCofiberSnd φ (i + 1) ≫ Q.d (i + 1) i :=
    homotopyCofiber.d_sndX φ (i + 1) i rfl
  rw [← Category.assoc, hd, Preadditive.add_comp]
  simp only [Category.assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CofiberConnecting
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The connecting homomorphism of the mapping-cone cochain sequence -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {k : Type} [CommRing k]

variable {G : Type} [Group G] {P Q : ChainComplex (Rep k G) ℕ}
  (φ : P ⟶ Q) (A : Rep k G)

theorem cofiberCochain_connecting (i : ℕ) :
    (cofiberCochainSequence_shortExact φ A).δ i (i + 1) (by simp) ≫
        (cochainSuccessorHomologyIso (P.linearYonedaObj k A) i).hom =
      HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i := by
  let C := P.linearYonedaObj k A
  let D := Q.linearYonedaObj k A
  let E := cochainSuccessor C
  let u := repCochainPrecomp k φ A
  let x₃ := D.iCycles i
  let x₂ := x₃ ≫ cofiberCochainSectionComponent φ A i
  let x := x₃ ≫ u.f i
  let x₁ := x ≫ (cochainSuccessorXIso C i).inv
  have hx₃ : x₃ ≫ D.d i (i + 1) = 0 := D.iCycles_d i (i + 1)
  have hx : x ≫ C.d i (i + 1) = 0 := by
    dsimp only [x]
    rw [Category.assoc, u.comm i (i + 1), ← Category.assoc, hx₃, zero_comp]
  have hx₂ : x₂ ≫ (cofiberCochainProjection φ A).f i = x₃ := by
    dsimp only [x₂]
    rw [Category.assoc, cofiberCochainSection_projection, Category.comp_id]
  have hx₁ : x₁ ≫ (cofiberCochainInclusion φ A).f (i + 1) =
      x₂ ≫ (ChainComplex.linearYonedaObj (repCofiber φ) k A).d i (i + 1) := by
    dsimp only [x₁, x, x₂]
    simp only [Category.assoc]
    rw [cofiberCochainSection_d, Preadditive.comp_add]
    rw [← Category.assoc x₃ (D.d i (i + 1)), hx₃, zero_comp, add_zero]
  have hs : x₁ ≫ E.d (i + 1) (i + 2) = 0 := by
    dsimp only [x₁]
    rw [Category.assoc, cochainSuccessor_d]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, Preadditive.comp_neg, hx, neg_zero, zero_comp]
  have hd := (cofiberCochainSequence_shortExact φ A).δ_eq i (i + 1) (by simp)
    x₃ hx₃ x₂ hx₂ x₁ hx₁ (i + 2) (by simp)
  change D.liftCycles x₃ (i + 1) (by simp) hx₃ ≫ D.homologyπ i ≫
      (cofiberCochainSequence_shortExact φ A).δ i (i + 1) (by simp) =
    E.liftCycles x₁ (i + 2) (by simp) hs ≫ E.homologyπ (i + 1) at hd
  have hid : D.liftCycles x₃ (i + 1) (by simp) hx₃ = 𝟙 (D.cycles i) := by
    apply (cancel_mono (D.iCycles i)).mp
    rw [liftCycles_i, Category.id_comp]
  rw [hid, Category.id_comp] at hd
  apply (cancel_epi (D.homologyπ i)).mp
  erw [← Category.assoc, hd]
  calc
    _ = D.liftCycles x₃ (i + 1) (by simp) hx₃ ≫
        HomologicalComplex.cyclesMap u i ≫ C.homologyπ i := by
      calc
        _ = E.liftCycles x₁ (i + 2) (by simp) hs ≫
            (E.homologyπ (i + 1) ≫ (cochainSuccessorHomologyIso C i).hom) :=
          Category.assoc _ _ _
        _ = C.liftCycles x (i + 1) (by simp) hx ≫ C.homologyπ i :=
          cochainSuccessor_liftCycles_homology C i x hx hs
        _ = _ := by rw [← Category.assoc, liftCycles_comp_cyclesMap]
    _ = D.homologyπ i ≫ HomologicalComplex.homologyMap u i := by
      rw [hid, Category.id_comp, homologyπ_naturality]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CofiberCohomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cohomology of a cone whose induced map is injective -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {k G : Type} [CommRing k] [Group G]
  {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q) (A : Rep k G)

theorem cofiberCochain_connecting_mono (i : ℕ)
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)] :
    Mono ((cofiberCochainSequence_shortExact φ A).δ i (i + 1) rfl) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y hxy
  apply (ModuleCat.mono_iff_injective
    (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)).mp inferInstance
  have h := cofiberCochain_connecting φ A i
  have hx := congrArg (fun f => f.hom x) h
  have hy := congrArg (fun f => f.hom y) h
  exact hx.symm.trans ((congrArg
    (cochainSuccessorHomologyIso (P.linearYonedaObj k A) i).hom.hom hxy).trans hy)

theorem cofiberCochain_homologyProjection_zero (i : ℕ)
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)] :
    HomologicalComplex.homologyMap (cofiberCochainProjection φ A) i = 0 := by
  let := cofiberCochain_connecting_mono φ A i
  have h := (cofiberCochainSequence_shortExact φ A).comp_δ i (i + 1) rfl
  change HomologicalComplex.homologyMap (cofiberCochainProjection φ A) i ≫
    (cofiberCochainSequence_shortExact φ A).δ i (i + 1) rfl = 0 at h
  exact (cancel_mono ((cofiberCochainSequence_shortExact φ A).δ i (i + 1) rfl)).mp
    (h.trans (zero_comp).symm)

theorem cofiberCochain_homologyInclusion_epi (i : ℕ)
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)] :
    Epi (HomologicalComplex.homologyMap (cofiberCochainInclusion φ A) i) :=
  ((cofiberCochainSequence_shortExact φ A).homology_exact₂ i).epi_f
    (cofiberCochain_homologyProjection_zero φ A i)

def cofiberCochainCokernelIso (i : ℕ)
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) (i + 1))] :
    cokernel (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i) ≅
      (ChainComplex.linearYonedaObj (repCofiber φ) k A).homology (i + 1) := by
  let S := cofiberCochainSequence φ A
  let hS := cofiberCochainSequence_shortExact φ A
  let : Epi (HomologicalComplex.homologyMap (cofiberCochainSequence φ A).f (i + 1)) :=
    cofiberCochain_homologyInclusion_epi φ A (i + 1)
  let e := cokernel.mapIso (hS.δ i (i + 1) rfl)
    (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)
    (Iso.refl _) (cochainSuccessorHomologyIso (P.linearYonedaObj k A) i)
    ((cofiberCochain_connecting φ A i).trans (Category.id_comp _).symm)
  exact e.symm ≪≫ (cokernelIsCokernel _).coconePointUniqueUpToIso
    (hS.homology_exact₁ i (i + 1) rfl).gIsCokernel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegerExtensionDuality
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cohomological dimension shift for an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)

section Cyclic
variable [IsCyclic (G ⧸ q.ker)] [Infinite (G ⧸ q.ker)]

variable (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))

attribute [local instance] OAI.PolycyclicRecognition.instCommGroupQuotientSubgroupKerMultiplicativeInt_solutions
def integerExtensionResolution : ProjectiveResolution (trivialIntegral G) :=
  cokernelProjectiveResolution
    (cyclicQuotientSequence (G ⧸ q.ker) (QuotientGroup.mk' q.ker) (QuotientGroup.mk' q.ker t))
    (quotientInducedResolution q.ker P) (quotientInducedResolution q.ker P)
    (cyclicQuotientSequence_shortExact (G ⧸ q.ker) (QuotientGroup.mk' q.ker)
      (QuotientGroup.mk' q.ker t) (integerQuotient_generator q t ht))

omit [Infinite (G ⧸ q.ker)] in
theorem integerExtensionMap_homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (repCochainPrecomp ℤ (integerExtensionMap q t P) (Rep.leftRegular ℤ G)) i =
        inducedCohomologyDifference q t P i :=
  (repCochainHomotopy ℤ (inducedCyclicDifferenceHomotopy q.ker t P)
    (Rep.leftRegular ℤ G)).homologyMap_eq i

end Cyclic

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FreeAbelianDuality
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free abelian rank bounds from integral cohomological dimension

The coordinate homomorphism splits off one infinite cyclic quotient at a time.
The resulting duality calculation bounds the rank of every embedded integral
lattice in a group of finite integral cohomological dimension.
-/

noncomputable section
namespace PolycyclicRecognition

def latticeCoordinateKernel (n : ℕ) : (latticeCoordinate n).ker ≃* IntegralLatticeGroup n where
  toFun a := Multiplicative.ofAdd (fun i => a.val.toAdd i.succ)
  invFun a := ⟨Multiplicative.ofAdd (Fin.cases 0 a.toAdd), by
    change latticeCoordinate n (Multiplicative.ofAdd (Fin.cases 0 a.toAdd)) = 1
    rfl⟩
  left_inv a := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    have ha : a.val.toAdd 0 = 0 := congrArg Multiplicative.toAdd a.property
    exact ha.symm
  right_inv a := rfl
  map_mul' _ _ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AbelianSubgroupRank
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.commutingIntegralHom_generator _root_.OAI.PolycyclicRecognition.integralQuotientDrop_insert _root_.OAI.PolycyclicRecognition.integralQuotientLast_insert _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Every abelian subgroup has bounded integral rank

An independent finite family defines an embedded integral lattice. The
cohomological-dimension bound on those lattices bounds the full module rank,
without assuming that the abelian subgroup is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {A : Type} [CommGroup A] {n : ℕ}

def independentLatticeHom (b : Fin n → Additive A) : IntegralLatticeGroup n →* A where
  toFun a := Additive.toMul (Fintype.linearCombination ℤ b a.toAdd)
  map_one' := by change Additive.toMul ((Fintype.linearCombination ℤ b) 0) = 1; simp
  map_mul' a c := congrArg Additive.toMul ((Fintype.linearCombination ℤ b).map_add a.toAdd c.toAdd)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ApproximateMidpointProper
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Properness of locally compact invariant metrics with approximate midpoints -/

namespace PolycyclicRecognition

open Set Metric Filter
open scoped Pointwise Topology

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G]

omit [IsTopologicalGroup G] in
theorem closedBall_subset_mul_of_approximateMidpoints
    (hmid : HasApproximateMidpoints G) {r : ℝ} (hr : 0 < r) :
    closedBall (1 : G) (3 * r / 2) ⊆ closedBall 1 r * closedBall 1 r := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hmid 1 x (r / 8) (by positivity)
  have hx' : dist (1 : G) x ≤ 3 * r / 2 := by
    simpa only [mem_closedBall, dist_comm] using hx
  refine ⟨z, ?_, z⁻¹ * x, ?_, by simp⟩
  · rw [mem_closedBall, dist_comm z 1]
    linarith
  · have heq : dist (z⁻¹ * x) 1 = dist z x := by
      rw [← dist_mul_left z, mul_inv_cancel_left, mul_one, dist_comm]
    rw [mem_closedBall, heq]
    linarith

theorem properSpace_of_approximateMidpoints [LocallyCompactSpace G]
    (hmid : HasApproximateMidpoints G) : ProperSpace G := by
  obtain ⟨r, hr, hcompact⟩ := exists_isCompact_closedBall (1 : G)
  have hc : ∀ n : ℕ, IsCompact (closedBall (1 : G) ((3 / 2 : ℝ) ^ n * r)) := by
    intro n
    induction n with
    | zero => simpa using hcompact
    | succ n ih =>
      apply (ih.mul ih).of_isClosed_subset isClosed_closedBall
      rw [show (3 / 2 : ℝ) ^ (n + 1) * r = 3 * ((3 / 2 : ℝ) ^ n * r) / 2 by
        rw [pow_succ]; ring]
      exact closedBall_subset_mul_of_approximateMidpoints hmid (by positivity)
  apply ProperSpace.of_seq_closedBall
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3 / 2)).atTop_mul_const hr)
  exact Filter.Eventually.of_forall hc

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CentralLayerTensor
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Tensor generators of a central commutator layer -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct commutatorElement IsMulCommutative
variable {G : Type} [Group G] (N : Subgroup G)
variable (h : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G)
  (K : Subgroup N) [K.Normal] [IsMulCommutative (N ⧸ K)]
  (hK : K.map N.subtype ≤ Subgroup.center G)

theorem centralLayerTensor_mem (x : Additive (Abelianization G) ⊗[ℤ] Additive (N ⧸ K)) :
    centralLayerTensor N h K hK x ∈ centralLayerSubmodule N := by
  induction x using OAI.tensorInductionOn with
  | tmul a b => exact centralLayerPairing_mem N h K hK a b
  | add x y hx hy =>
    simpa only [map_add] using (centralLayerSubmodule N).add_mem hx hy

def centralLayerTensorSurjection :
    (Additive (Abelianization G) ⊗[ℤ] Additive (N ⧸ K)) →ₗ[ℤ] centralLayerSubmodule N :=
  (centralLayerTensor N h K hK).codRestrict _ (centralLayerTensor_mem N h K hK)

theorem centralLayerTensor_range :
    LinearMap.range (centralLayerTensor N h K hK) = centralLayerSubmodule N := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact centralLayerTensor_mem N h K hK x
  · let U := (LinearMap.range (centralLayerTensor N h K hK)).toAddSubgroup.toSubgroup
    let P := U.map (Subgroup.center G).subtype
    have hP : ⁅(⊤ : Subgroup G), N⁆ ≤ P := by
      apply Subgroup.commutator_le.mpr
      intro a _ b hb
      let bN : N := ⟨b, hb⟩
      let z := centralLayerPairing N h K hK (Additive.ofMul (Abelianization.of a))
        (Additive.ofMul ((QuotientGroup.mk' K) bN))
      refine ⟨z.toMul, ?_, rfl⟩
      exact ⟨Additive.ofMul (Abelianization.of a) ⊗ₜ[ℤ]
        Additive.ofMul ((QuotientGroup.mk' K) bN), rfl⟩
    intro x hx
    obtain ⟨z, hz, he⟩ := hP hx
    have he' : z = x.toMul := Subtype.ext he
    change Additive.ofMul z ∈ LinearMap.range (centralLayerTensor N h K hK) at hz
    simpa only [he', ofMul_toMul] using hz

theorem centralLayerTensor_surjective :
    Function.Surjective (centralLayerTensorSurjection N h K hK) := by
  intro z
  obtain ⟨x, hx⟩ := (show (z : Additive (Subgroup.center G)) ∈
      LinearMap.range (centralLayerTensor N h K hK) by
    rw [centralLayerTensor_range N h K hK]
    exact z.property)
  exact ⟨x, Subtype.ext hx⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CoefficientNaturalCohomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient naturality for cohomology from a chosen resolution

The comparison uses one fixed homotopy equivalence with the bar resolution.
Consequently it commutes with every coefficient morphism.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] {A B : Rep.{0} ℤ G}

theorem repCochainPrecomp_postcomp {P Q : ChainComplex (Rep.{0} ℤ G) ℕ}
    (u : P ⟶ Q) (f : A ⟶ B) :
    repCochainPrecomp ℤ u A ≫ repCochainPostcomp ℤ P f =
      repCochainPostcomp ℤ Q f ≫ repCochainPrecomp ℤ u B := by
  ext i v
  change (u.f i ≫ v) ≫ f = u.f i ≫ (v ≫ f)
  exact Category.assoc _ _ _

theorem inhomogeneousCochainsIso_coefficient (f : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id G) f ≫
        (groupCohomology.inhomogeneousCochainsIso B).hom =
      (groupCohomology.inhomogeneousCochainsIso A).hom ≫
        repCochainPostcomp ℤ (Rep.barComplex ℤ G) f := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply DFunLike.ext
  intro v
  change (Fin i → G) → A at v
  apply Rep.free_ext
  intro t
  change B.ρ.freeLift (fun x => f.hom (v x))
      (Finsupp.single t (MonoidAlgebra.single 1 1)) =
    f.hom (A.ρ.freeLift v (Finsupp.single t (MonoidAlgebra.single 1 1)))
  simp only [Representation.freeLift_single_single, map_one, Module.End.one_apply]
  exact (f.hom.map_smul (1 : ℤ) (v t)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ResolutionCoefficientSequence
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short exact coefficient sequences in a projective-resolution Hom complex -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def resolutionCoefficientSequence (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (S : ShortComplex (Rep.{0} ℤ G)) : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (repCochainPostcomp ℤ P.complex S.f) (repCochainPostcomp ℤ P.complex S.g)
    (by
      ext i v
      change P.complex.X i ⟶ S.X₁ at v
      change (v ≫ S.f) ≫ S.g = 0
      rw [Category.assoc, S.zero, comp_zero])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoefficientConnectingNaturality
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connecting homomorphisms commute with the chosen-resolution comparison -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def coefficientNaturalCochainMap (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (A : Rep.{0} ℤ G) :
    groupCohomology.inhomogeneousCochains A ⟶ P.complex.linearYonedaObj ℤ A :=
  (groupCohomology.inhomogeneousCochainsIso A).hom ≫
    repCochainPrecomp ℤ (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)).hom A

theorem coefficientNaturalCochainMap_naturality
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id G) f ≫ coefficientNaturalCochainMap P B =
      coefficientNaturalCochainMap P A ≫ repCochainPostcomp ℤ P.complex f := by
  dsimp [coefficientNaturalCochainMap]
  erw [← Category.assoc, inhomogeneousCochainsIso_coefficient,
    Category.assoc, ← repCochainPrecomp_postcomp, ← Category.assoc]

def coefficientComparisonSequenceMap (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (S : ShortComplex (Rep.{0} ℤ G)) :
    S.map (groupCohomology.cochainsFunctor ℤ G) ⟶ resolutionCoefficientSequence P S where
  τ₁ := coefficientNaturalCochainMap P S.X₁
  τ₂ := coefficientNaturalCochainMap P S.X₂
  τ₃ := coefficientNaturalCochainMap P S.X₃
  comm₁₂ := (coefficientNaturalCochainMap_naturality P S.f).symm
  comm₂₃ := (coefficientNaturalCochainMap_naturality P S.g).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_InvariantMean
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive normalized left-invariant means

The domain is the actual space of all bounded real functions on the group.
Continuity is a consequence of positivity and normalization, not an assumption.
-/

noncomputable section

open scoped ENNReal

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G]

/-- Pullback reverses the order of the two left multiplications. -/
theorem leftPull_mul (h k : G) (f : BoundedReal G) :
    leftPull (h * k) f = leftPull k (leftPull h f) := by
  apply lp.ext
  funext g
  simp [mul_assoc]

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseEquivalence
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coarse equivalences of discrete groups

Finite subsets are the bounded sets in a word metric on a finitely generated
group. Controlling all finite sets of differences is the metric-free form of
being bornologous. For finitely generated groups, a coarse equivalence in this
sense is a quasi-isometry. It also matches the coarse-equivalence formulation
of Li's finiteness and duality theorems.
-/

namespace PolycyclicRecognition

open scoped Pointwise

variable {G H J : Type*} [Group G] [Group H] [Group J]

theorem finite_rightCosetRepresentatives (K : Subgroup G) [K.FiniteIndex] :
    (Set.range (rightCosetRepresentative K)).Finite := by
  have : Finite (Quotient (QuotientGroup.rightRel K)) :=
    Finite.of_equiv (G ⧸ K) (QuotientGroup.quotientRightRelEquivQuotientLeftRel K).symm
  apply (Set.finite_range (fun q : Quotient (QuotientGroup.rightRel K) => q.out)).subset
  rintro _ ⟨g, rfl⟩
  exact ⟨Quotient.mk'' g, rfl⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TorsionFreeAbelianRank
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Uniform rank bounds on finitely generated abelian subgroups

A torsion-free finitely generated abelian group is an integral lattice. The
explicit lattice duality calculation therefore bounds the rank of every such
subgroup by a common ambient cohomological-dimension bound.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {A : Type} [CommGroup A]

def integralLatticeEquivOfBasis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Additive A)) :
    IntegralLatticeGroup n ≃* A where
  toFun a := Additive.toMul (b.equivFun.symm a.toAdd)
  invFun a := Multiplicative.ofAdd (b.equivFun (Additive.ofMul a))
  left_inv a := by
    change Multiplicative.ofAdd (b.equivFun (b.equivFun.symm a.toAdd)) = a
    rw [LinearEquiv.apply_symm_apply]
    rfl
  right_inv a := by
    change Additive.toMul (b.equivFun.symm (b.equivFun (Additive.ofMul a))) = a
    rw [LinearEquiv.symm_apply_apply]
    rfl
  map_mul' a b' := congrArg Additive.toMul (b.equivFun.symm.map_add a.toAdd b'.toAdd)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FreeAbelianLogarithm
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible logarithms of characters of free abelian groups

Choosing logarithms only on a basis preserves all multiplicative relations.
-/

noncomputable section
namespace PolycyclicRecognition

def freeAbelianLogarithm {n : ℕ} (ρ : IntegralLatticeGroup n →* ℂˣ) :
    IntegralLatticeGroup n →* Multiplicative ℂ := by
  let f := (Pi.basisFun ℤ (Fin n)).constr ℤ
    (fun i => Complex.log (ρ (Multiplicative.ofAdd ((Pi.basisFun ℤ (Fin n)) i)) : ℂ))
  exact f.toAddMonoidHom.toMultiplicative

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexifiedLieAutomorphism
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complexification of a real semisimple Lie automorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct

variable (L : Type) [LieRing L] [LieAlgebra ℝ L]

@[instance_reducible] def complexificationNormedLie [FiniteDimensional ℝ L] :
    ComplexNormedLieAlgebra (ℂ ⊗[ℝ] L) := by
  let b := Module.finBasis ℂ (ℂ ⊗[ℝ] L)
  let : NormedAddCommGroup (ℂ ⊗[ℝ] L) :=
    NormedAddCommGroup.induced _ _ b.equivFun b.equivFun.injective
  let : NormedSpace ℂ (ℂ ⊗[ℝ] L) := NormedSpace.induced ℂ _ _ b.equivFun
  exact { (inferInstance : NormedAddCommGroup (ℂ ⊗[ℝ] L)),
    (inferInstance : LieRing (ℂ ⊗[ℝ] L)), (inferInstance : NormedSpace ℂ (ℂ ⊗[ℝ] L)),
    (inferInstance : LieAlgebra ℂ (ℂ ⊗[ℝ] L)) with }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexDerivationDescent
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending a conjugation-invariant complex derivation -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable (L : Type) [LieRing L] [LieAlgebra ℝ L]

theorem complexificationRealPart_one_lie (x : L) (y : ℂ ⊗[ℝ] L) :
    complexificationRealPart L ⁅(1 : ℂ) ⊗ₜ[ℝ] x, y⁆ =
      ⁅x, complexificationRealPart L y⁆ := by
  rw [← lie_skew ((1 : ℂ) ⊗ₜ[ℝ] x) y, map_neg,
    complexificationRealPart_lie_one, lie_skew]

def complexDerivationRealPart (D : LieDerivation ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L)) :
    LieDerivation ℝ L L :=
  { toLinearMap := (complexificationRealPart L).comp
      ((D.toLinearMap.restrictScalars ℝ).comp (complexificationLieHom L).toLinearMap)
    leibniz' := by
      intro x y
      change complexificationRealPart L (D ((1 : ℂ) ⊗ₜ[ℝ] ⁅x, y⁆)) = _
      rw [show (1 : ℂ) ⊗ₜ[ℝ] ⁅x, y⁆ =
          ⁅(1 : ℂ) ⊗ₜ[ℝ] x, (1 : ℂ) ⊗ₜ[ℝ] y⁆ by simp,
        D.apply_lie_eq_sub, map_sub, complexificationRealPart_one_lie,
        complexificationRealPart_one_lie]
      rfl }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomogeneousCochainCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates for scalar homogeneous cochains

The first vertex records translation and the remaining vertices record
relative positions. This identifies controlled-support homogeneous cochains
with arbitrary cochains valued in the group ring.
-/

noncomputable section
namespace PolycyclicRecognition
open Function

variable {G : Type*} [Group G] {n : ℕ}

variable {R : Type*} [CommRing R]

/-- Arbitrary group-ring-valued cochains have finite support at each
controlled scale after passing to scalar homogeneous coordinates. -/
theorem controlled_homogeneous_of_finsupp (f : (Fin n → G) → (G →₀ R)) :
    (fun x => f (homogeneousCoordinates x).1 (homogeneousCoordinates x).2) ∈
      controlledCochains R G n := by
  classical
  intro S hS
  let A : Set (Fin n → G) := {a | ∀ i, a i ∈ S}
  have hA : A.Finite := Set.Finite.pi' (fun _ => hS)
  let B : Set ((Fin n → G) × G) := ⋃ a ∈ A, (fun h => (a, h)) '' (f a).support
  have hB : B.Finite := hA.biUnion (fun a _ => (f a).support.finite_toSet.image _)
  apply (hB.preimage homogeneousCoordinates.injective.injOn).subset
  intro x hx
  apply Set.mem_iUnion.mpr
  refine ⟨(homogeneousCoordinates x).1, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · intro i
    exact hx.1 0 i.succ
  · refine ⟨(homogeneousCoordinates x).2, ?_, rfl⟩
    exact Finsupp.mem_support_iff.mpr hx.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledGroupRingCoefficients
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledCoboundary_apply _root_.OAI.PolycyclicRecognition.controlledCochainComplex_d _root_.OAI.PolycyclicRecognition.controlledCochainMap_apply _root_.OAI.PolycyclicRecognition.controlledFace_apply _root_.OAI.PolycyclicRecognition.controlledLinearExtension_single _root_.OAI.PolycyclicRecognition.controlledPrismHom_succ _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering group-ring coefficients from controlled scalar cochains

Diagonal translation turns a scalar cochain into a finitely supported
coefficient function. The covariance formula is the actual left regular
action needed to identify these cochains with the standard group resolution.
-/

noncomputable section
namespace PolycyclicRecognition
open Function
variable {G R : Type*} [Group G] [CommRing R] {n : ℕ}

/-- Only finitely many diagonal translates of a fixed tuple can have a
nonzero value under a controlled cochain. -/
theorem finite_support_diagonal_translate (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) :
    (support (fun h => c (fun i => h⁻¹ * x i))).Finite := by
  let S : Set G := Set.range (fun p : Fin (n + 1) × Fin (n + 1) => (x p.1)⁻¹ * x p.2)
  have hS : S.Finite := Set.finite_range _
  have hi : Injective (fun h : G => fun i : Fin (n + 1) => h⁻¹ * x i) := by
    intro a b hab
    exact inv_injective (mul_right_cancel (congrFun hab 0))
  apply ((c.property S hS).preimage hi.injOn).subset
  intro h hh
  refine ⟨?_, hh⟩
  intro i j
  refine ⟨(i, j), ?_⟩
  simp [mul_assoc]

/-- The group-ring value of a scalar homogeneous cochain. -/
def controlledGroupRingValue (c : controlledCochains R G n) (x : Fin (n + 1) → G) :
    G →₀ R := Finsupp.ofSupportFinite (fun h => c (fun i => h⁻¹ * x i))
      (finite_support_diagonal_translate c x)

@[simp] theorem controlledGroupRingValue_apply (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (h : G) :
    controlledGroupRingValue c x h = c (fun i => h⁻¹ * x i) := rfl

@[simp] theorem controlledGroupRingValue_one (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) : controlledGroupRingValue c x 1 = c x := by
  simp

/-- Equivariance is forced by diagonal translation; the group action is
not inserted as an assumption on the coarse map. -/
theorem controlledGroupRingValue_covariance (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (g h : G) :
    controlledGroupRingValue c (fun i => g * x i) h =
      controlledGroupRingValue c x (g⁻¹ * h) := by
  simp [mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TuplePrism
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The simplicial prism on tuples

The universal homogeneous simplex on a set has one simplex for every tuple.
Two maps of vertices are joined by the prism that uses the first map before
a chosen vertex and the second map afterwards.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped Simplicial

variable {A B : Type} {n : ℕ}

theorem tuplePrism_first_face (f g : A → B) (x : Fin (n + 1) → A) :
    tuplePrism f g 0 x ∘ (0 : Fin (n + 2)).succAbove = g ∘ x := by
  funext k
  simp [tuplePrism, Fin.succAbove_zero]

theorem tuplePrism_last_face (f g : A → B) (x : Fin (n + 1) → A) :
    tuplePrism f g (Fin.last n) x ∘ (Fin.last (n + 1)).succAbove = f ∘ x := by
  funext k
  simp [tuplePrism, Fin.succAbove_last, Nat.le_of_lt_succ k.isLt]

theorem tupleSuccAbove_val {m : ℕ} (i : Fin (m + 1)) (k : Fin m) :
    (i.succAbove k).val = if k.val < i.val then k.val else k.val + 1 := by
  by_cases h : k.val < i.val
  · have h' : k.castSucc < i := h
    rw [Fin.succAbove, ite_eq_left h', ite_eq_left h]
    rfl
  · have h' : ¬k.castSucc < i := h
    rw [Fin.succAbove, ite_eq_right h', ite_eq_right h]
    rfl

theorem tuplePredAbove_val {m : ℕ} (i : Fin m) (k : Fin (m + 1)) :
    (i.predAbove k).val = if i.val < k.val then k.val - 1 else k.val := by
  by_cases h : i.val < k.val
  · have h' : i.castSucc < k := h
    rw [Fin.predAbove, dite_eq_left h', ite_eq_left h]
    rfl
  · have h' : ¬i.castSucc < k := h
    rw [Fin.predAbove, dite_eq_right h', ite_eq_right h]
    rfl

theorem tuplePrism_face_before (f g : A → B) (i : Fin (n + 2))
    (j : Fin (n + 1)) (hij : i ≤ j.castSucc) (x : Fin (n + 2) → A) :
    tuplePrism f g j.succ x ∘ i.castSucc.succAbove =
      tuplePrism f g j (x ∘ i.succAbove) := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tupleSuccAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals try simp only [Fin.le_def, Fin.val_castSucc] at *
  all_goals first | omega | (congr 2; apply Fin.ext)
  all_goals simp only [tupleSuccAbove_val]
  all_goals split_ifs <;> omega

theorem tuplePrism_face_middle (f g : A → B) (j : Fin (n + 1))
    (x : Fin (n + 2) → A) :
    tuplePrism f g j.succ x ∘ j.castSucc.succ.succAbove =
      tuplePrism f g j.castSucc x ∘ j.castSucc.succ.succAbove := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tupleSuccAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals first | rfl | omega

theorem tuplePrism_face_after (f g : A → B) (i : Fin (n + 2))
    (j : Fin (n + 1)) (hji : j.castSucc < i) (x : Fin (n + 2) → A) :
    tuplePrism f g j.castSucc x ∘ i.succ.succAbove =
      tuplePrism f g j (x ∘ i.succAbove) := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tupleSuccAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals try simp only [Fin.lt_def, Fin.val_castSucc] at *
  all_goals first | omega | (congr 2; apply Fin.ext)
  all_goals simp only [tupleSuccAbove_val]
  all_goals split_ifs <;> omega

theorem tuplePrism_degeneracy_before (f g : A → B) (i j : Fin (n + 1))
    (hij : i ≤ j) (x : Fin (n + 1) → A) :
    tuplePrism f g j x ∘ i.castSucc.predAbove =
      tuplePrism f g j.succ (x ∘ i.predAbove) := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tuplePredAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals try simp only [Fin.le_def] at *
  all_goals first | omega | (congr 2; apply Fin.ext)
  all_goals simp only [tuplePredAbove_val]
  all_goals split_ifs <;> omega

theorem tuplePrism_degeneracy_after (f g : A → B) (i j : Fin (n + 1))
    (hji : j ≤ i) (x : Fin (n + 1) → A) :
    tuplePrism f g j x ∘ i.succ.predAbove =
      tuplePrism f g j.castSucc (x ∘ i.predAbove) := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tuplePredAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals try simp only [Fin.le_def] at *
  all_goals first | omega | (congr 2; apply Fin.ext)
  all_goals simp only [tuplePredAbove_val]
  all_goals split_ifs <;> omega

/-- The usual prism is a genuine simplicial homotopy. -/
def tupleSimplicialHomotopy (f g : A → B) :
    SimplicialObject.Homotopy (tupleSimplicialMap f) (tupleSimplicialMap g) where
  h i := ↾tuplePrism f g i
  h_zero_comp_δ_zero _ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_first_face f g x
  h_last_comp_δ_last _ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_last_face f g x
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_face_before f g i j hij x
  h_succ_comp_δ_castSucc_succ j := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_face_middle f g j x
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_face_after f g i j hji x
  h_comp_σ_castSucc_of_le i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_degeneracy_before f g i j hij x
  h_comp_σ_succ_of_lt i j hji := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_degeneracy_after f g i j hji x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TupleChainPrism
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prism on free homogeneous chains

Linearization of the tuple homotopy gives the chain homotopy. The formulas
below identify its components with the alternating prism and boundary.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped Simplicial
variable {A B R : Type} [CommRing R]

def tupleChainPrism (f g : A → B) : Homotopy (tupleChainMap (R := R) f) (tupleChainMap g) :=
  ((tupleSimplicialHomotopy f g).whiskerRight (ModuleCat.monoidAlgebraFree R)).toChainHomotopy

theorem tupleChainComplex_boundary (n : ℕ) (x : Fin (n + 2) → A) :
    (tupleChainComplex R A).d (n + 1) n (MonoidAlgebra.single x 1) =
      ∑ i : Fin (n + 2), (-1 : R) ^ i.val • MonoidAlgebra.single (x ∘ i.succAbove) 1 := by
  change ((tupleChainComplex R A).d (n + 1) n).hom (MonoidAlgebra.single x 1) = _
  simp [tupleChainComplex, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    tupleFreeSimplicial, tupleSimplicial, SimplicialObject.δ, SimplexCategory.δ,
    Fin.succAboveOrderEmb, ModuleCat.monoidAlgebraFree, ← Int.cast_smul_eq_zsmul R]
  erw [LinearMap.sum_apply]
  simp

theorem tupleChainPrism_single (f g : A → B) (n : ℕ) (x : Fin (n + 1) → A) :
    (tupleChainPrism (R := R) f g).hom n (n + 1) (MonoidAlgebra.single x 1) =
      -∑ i : Fin (n + 1), (-1 : R) ^ i.val • MonoidAlgebra.single (tuplePrism f g i x) 1 := by
  change ((tupleChainPrism (R := R) f g).hom n (n + 1)).hom
    (MonoidAlgebra.single x 1) = _
  simp only [tupleChainPrism, SimplicialObject.Homotopy.toChainHomotopy,
    SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    SimplicialObject.Homotopy.whiskerRight, tupleSimplicialHomotopy,
    ModuleCat.monoidAlgebraFree]
  erw [ModuleCat.hom_neg, ModuleCat.hom_sum]
  erw [LinearMap.neg_apply, LinearMap.sum_apply]
  change -(∑ i : Fin (n + 1), ((-1 : ℤ) ^ i.val) •
    (MonoidAlgebra.mapDomainLinearMap R R (tuplePrism f g i)
      (MonoidAlgebra.single x 1))) = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [MonoidAlgebra.mapDomainLinearMap_single]
  simp [← Int.cast_smul_eq_zsmul R]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ControlledCochainMap
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse pullback as a map of controlled cochain complexes -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G H J R : Type} [Group G] [Group H] [Group J] [CommRing R]

/-- Pullback on complexes reverses composition. -/
theorem controlledCochainMap_trans (e : GroupCoarseEquivalence G H)
    (e' : GroupCoarseEquivalence H J) :
    controlledCochainMap (R := R) (e.trans e') =
      controlledCochainMap e' ≫ controlledCochainMap e := by
  ext n c
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledPrismIdentity
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledGroupRingValue_apply _root_.OAI.PolycyclicRecognition.controlledGroupRingValue_one _root_.OAI.PolycyclicRecognition.controlledPrismHom_succ _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The controlled prism identity

The identity is inherited from the actual simplicial chain homotopy, after
the support estimate has placed every summand in the controlled complex.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G H R : Type} [Group G] [Group H] [CommRing R] {n : ℕ}

def controlledLinearExtensionMap :
    controlledCochains R G n →ₗ[R] (MonoidAlgebra R (Fin (n + 1) → G) →ₗ[R] R) where
  toFun := controlledLinearExtension
  map_add' c d := by
    refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
    simp [mul_add]
  map_smul' r c := by
    refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
    simp

theorem controlledLinearExtension_injective :
    Function.Injective (controlledLinearExtension (R := R) (G := G) (n := n)) := by
  intro c d h
  apply Subtype.ext
  funext x
  have hx := congrArg (fun f => f (MonoidAlgebra.single x 1)) h
  simpa using hx

omit [Group G] in
theorem tupleChainComplex_boundary_linear :
    ((tupleChainComplex R G).d (n + 1) n).hom = Rep.standardComplex.d R G (n + 1) := by
  refine MonoidAlgebra.lhom_ext' fun (x : Fin (n + 2) → G) => LinearMap.ext_ring ?_
  change (tupleChainComplex R G).d (n + 1) n (MonoidAlgebra.single x 1) =
    Rep.standardComplex.d R G (n + 1) (MonoidAlgebra.single x 1)
  rw [tupleChainComplex_boundary, Rep.standardComplex.d_single]
  simp
  rfl

theorem controlledLinearExtension_pullback (e : GroupCoarseEquivalence G H)
    (c : controlledCochains R H n) :
    controlledLinearExtension (controlledCochainPullback e n c) =
      (controlledLinearExtension c).comp ((tupleChainMap e.toFun).f n).hom := by
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  change controlledLinearExtension (controlledCochainPullback e n c) (MonoidAlgebra.single x 1) =
    controlledLinearExtension c ((tupleChainMap e.toFun).f n (MonoidAlgebra.single x 1))
  rw [tupleChainMap_single]
  simp

theorem controlledLinearExtension_prism (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (c : controlledCochains R H (n + 1)) :
    controlledLinearExtension (controlledPrism e e' hc c) =
      (controlledLinearExtension c).comp
        ((tupleChainPrism e.toFun e'.toFun).hom n (n + 1)).hom := by
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  change controlledLinearExtension (controlledPrism e e' hc c) (MonoidAlgebra.single x 1) =
    controlledLinearExtension c
      ((tupleChainPrism e.toFun e'.toFun).hom n (n + 1) (MonoidAlgebra.single x 1))
  rw [tupleChainPrism_single]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledPrismEquation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledGroupRingValue_apply _root_.OAI.PolycyclicRecognition.controlledGroupRingValue_one _root_.OAI.PolycyclicRecognition.controlledPrismHom_succ _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cochain equation for the controlled prism -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {G H R : Type} [Group G] [Group H] [CommRing R] {n : ℕ}

theorem controlledPrism_equation_succ (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (c : controlledCochains R H (n + 1)) :
    controlledCochainPullback e (n + 1) c =
      controlledCoboundary (controlledPrism e e' hc c) +
        controlledPrism e e' hc (controlledCoboundary c) +
          controlledCochainPullback e' (n + 1) c := by
  have h := (tupleChainPrism (R := R) e.toFun e'.toFun).comm (n + 1)
  rw [dNext_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
    prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at h
  have hh := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp] at hh
  apply controlledLinearExtension_injective
  change controlledLinearExtensionMap _ = controlledLinearExtensionMap _
  simp only [map_add]
  change controlledLinearExtension (controlledCochainPullback e (n + 1) c) =
    controlledLinearExtension (controlledCoboundary (controlledPrism e e' hc c)) +
      controlledLinearExtension (controlledPrism e e' hc (controlledCoboundary c)) +
        controlledLinearExtension (controlledCochainPullback e' (n + 1) c)
  rw [controlledLinearExtension_pullback, controlledLinearExtension_coboundary,
    controlledLinearExtension_prism, controlledLinearExtension_prism,
    controlledLinearExtension_coboundary, controlledLinearExtension_pullback,
    ← tupleChainComplex_boundary_linear, ← tupleChainComplex_boundary_linear, hh]
  erw [LinearMap.comp_add, LinearMap.comp_add]
  rfl

theorem controlledPrism_equation_zero (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (c : controlledCochains R H 0) :
    controlledCochainPullback e 0 c =
      controlledPrism e e' hc (controlledCoboundary c) + controlledCochainPullback e' 0 c := by
  have h := (tupleChainPrism (R := R) e.toFun e'.toFun).comm 0
  rw [dNext_eq_zero _ _ (by simp),
    prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel 1 0), zero_add] at h
  have hh := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp] at hh
  apply controlledLinearExtension_injective
  change controlledLinearExtensionMap _ = controlledLinearExtensionMap _
  simp only [map_add]
  change controlledLinearExtension (controlledCochainPullback e 0 c) =
      controlledLinearExtension (controlledPrism e e' hc (controlledCoboundary c)) +
        controlledLinearExtension (controlledCochainPullback e' 0 c)
  rw [controlledLinearExtension_pullback, controlledLinearExtension_prism,
    controlledLinearExtension_coboundary, controlledLinearExtension_pullback,
    ← tupleChainComplex_boundary_linear, hh]
  erw [LinearMap.comp_add]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationarySlope
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging the stationary height cocycle

The normalized pair space carries a measure-preserving action. Its height
evaluation is a cocycle for inverse pullback. We construct that action on the
actual space `L²`, and show that integration gives an additive slope. No
reduced-cohomology assertion is assumed in this construction.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter

variable {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X]
  [NormedAddCommGroup W]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

theorem stationaryPullback_one (v : Lp W 2 μ) : stationaryPullback μ (1 : G) v = v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving v (measurePreserving_smul (1 : G)⁻¹ μ)]
    with x hx
  exact hx.trans (by simp)

theorem stationaryPullback_mul (g h : G) (v : Lp W 2 μ) :
    stationaryPullback μ (g * h) v =
      stationaryPullback μ g (stationaryPullback μ h v) := by
  simpa only [stationaryPullback, mul_inv_rev, mul_smul, Function.comp_def] using
    Lp.compMeasurePreserving_comp_apply v (measurePreserving_smul h⁻¹ μ)
      (measurePreserving_smul g⁻¹ μ)

/-- The isometric additive action on the genuine `L²` space. -/
@[instance_reducible]
def stationaryL2Action : DistribMulAction G (Lp W 2 μ) where
  smul g v := stationaryPullback μ g v
  one_smul := stationaryPullback_one μ
  mul_smul := stationaryPullback_mul μ
  smul_zero g := (stationaryPullback (W := W) μ g).map_zero
  smul_add g x y := (stationaryPullback (W := W) μ g).map_add x y

attribute [local instance] stationaryL2Action

variable [NormedSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace W] in
/-- The mean is invariant under the pullback representation. -/
theorem stationaryL2Mean_pullback [IsProbabilityMeasure μ] (g : G) (v : Lp W 2 μ) :
    stationaryL2Mean μ (stationaryPullback μ g v) = stationaryL2Mean μ v := by
  change (∫ x, (stationaryPullback μ g v) x ∂μ) = ∫ x, v x ∂μ
  calc
    (∫ x, (stationaryPullback μ g v) x ∂μ) = ∫ x, v (g⁻¹ • x) ∂μ :=
      integral_congr_ae (Lp.coeFn_compMeasurePreserving v (measurePreserving_smul g⁻¹ μ))
    _ = _ := (measurePreserving_smul g⁻¹ μ).integral_comp
      (measurableEmbedding_const_smul g⁻¹) _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ControlledProductPairs
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled Følner pairs from compact product coordinates

The required estimate is an explicit right-product containment in a larger
rectangle, together with a bounded ratio of the two coordinate volumes.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set Filter
open scoped ENNReal

variable {G N D : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace N] [TopologicalSpace D] [T2Space N] [T2Space D]
  [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D]
  (e : G ≃ₜ N × D) (μN : Measure N) (μD : Measure D)
  [SFinite μN] [SFinite μD] [IsFiniteMeasureOnCompacts μN] [IsFiniteMeasureOnCompacts μD]

def controlledMetricFolnerPairs_of_product_sets
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n) (hlim : Tendsto scale atTop atTop)
    (A A' : ℕ → Set N) (B B' : ℕ → Set D)
    (hA : ∀ n, IsCompact (A n)) (hA' : ∀ n, IsCompact (A' n))
    (hB : ∀ n, IsCompact (B n)) (hB' : ∀ n, IsCompact (B' n))
    (hneA : ∀ n, (A n).Nonempty) (hneB : ∀ n, (B n).Nonempty)
    (hposA : ∀ n, 0 < μN.real (A n)) (hposB : ∀ n, 0 < μD.real (B n))
    {R CN CD : ℝ} (hR : 0 ≤ R) (hCN : 0 ≤ CN) (hCD : 0 ≤ CD)
    (hrad : ∀ n x, e x ∈ A n ×ˢ B n → dist 1 x ≤ R * scale n)
    (hmul : ∀ n x, e x ∈ A n ×ˢ B n → ∀ y, dist 1 y ≤ 2 * scale n →
      e (x * y) ∈ A' n ×ˢ B' n)
    (hvolA : ∀ n, μN.real (A' n) ≤ CN * μN.real (A n))
    (hvolB : ∀ n, μD.real (B' n) ≤ CD * μD.real (B n)) :
    ControlledMetricFolnerPairs (Measure.map e.symm (μN.prod μD)) := by
  let μ := Measure.map e.symm (μN.prod μD)
  let S := fun n => e ⁻¹' (A n ×ˢ B n)
  have hc (n : ℕ) : IsCompact (S n) := e.isCompact_preimage.mpr ((hA n).prod (hB n))
  have hn (n : ℕ) : (S n).Nonempty := by
    obtain ⟨a, ha⟩ := hneA n
    obtain ⟨b, hb⟩ := hneB n
    refine ⟨e.symm (a, b), ?_⟩
    change e (e.symm (a, b)) ∈ A n ×ˢ B n
    rw [e.apply_symm_apply]
    exact ⟨ha, hb⟩
  have heq (n : ℕ) : μ.real (S n) = μN.real (A n) * μD.real (B n) := by
    rw [measureReal_def, productCoordinateMeasure_rectangle e μN μD
      (hA n).measurableSet (hB n).measurableSet, ENNReal.toReal_mul]
    rfl
  refine {
    scale := scale, scale_pos := hscale, scale_tendsto := hlim,
    sets := S, compact := hc, nonempty := hn,
    positive := fun n => (heq n).symm ▸ mul_pos (hposA n) (hposB n),
    radiusConstant := R, radius_nonneg := hR, radius_bound := hrad,
    volumeConstant := CN * CD, volume_nonneg := mul_nonneg hCN hCD,
    volume_bound := ?_ }
  intro n
  have hs0 := (hscale n).le
  have hsub : cthickening (2 * scale n) (S n) ⊆ e ⁻¹' (A' n ×ˢ B' n) := by
    intro z hz
    have hi : infDist z (S n) ≤ 2 * scale n := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hz
      simpa only [infDist, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * scale n)] using h
    obtain ⟨x, hx, hdist⟩ := (hc n).exists_infDist_eq_dist (hn n) z
    have hxy : dist 1 (x⁻¹ * z) ≤ 2 * scale n := by
      have he : dist 1 (x⁻¹ * z) = dist z x := by
        simpa only [mul_one, mul_inv_cancel_left, dist_comm] using
          (dist_mul_left x (1 : G) (x⁻¹ * z)).symm
      rw [he, ← hdist]
      exact hi
    have h := hmul n x hx (x⁻¹ * z) hxy
    change e z ∈ A' n ×ˢ B' n
    simpa only [mul_inv_cancel_left] using h
  have hf : μ (e ⁻¹' (A' n ×ˢ B' n)) ≠ ∞ := by
    rw [productCoordinateMeasure_rectangle e μN μD (hA' n).measurableSet (hB' n).measurableSet]
    exact ENNReal.mul_ne_top (hA' n).measure_ne_top (hB' n).measure_ne_top
  have hm := ENNReal.toReal_mono hf (measure_mono (μ := μ) hsub)
  rw [productCoordinateMeasure_rectangle e μN μD (hA' n).measurableSet (hB' n).measurableSet,
    ENNReal.toReal_mul] at hm
  rw [heq]
  exact hm.trans ((mul_le_mul (hvolA n) (hvolB n) (measureReal_nonneg)
    (mul_nonneg hCN measureReal_nonneg)).trans_eq (by ring))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactPairs
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact sections of Lipschitz quasi-inverse pairs

The space consists of actual continuous maps, with the compact-open topology.
Uniform Lipschitz bounds and a bound at one point give compactness in a proper
target. The quasi-inverse conditions are closed, including their compositions.
-/

noncomputable section

open Set Metric
open scoped NNReal

namespace PolycyclicRecognition

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [ProperSpace Y]

variable (G : Type*) [Group G] [MetricSpace G] [ProperSpace G]

omit [Group G] in
theorem isClosed_lipschitzPairBounds (Λ : ℝ≥0) :
    IsClosed {p | LipschitzPairBounds G Λ p} := by
  have hcoe : Continuous (fun f : C(G, G) => (f : G → G)) :=
    continuous_pi fun x => continuous_eval_const x
  have hl : IsClosed {f : C(G, G) | LipschitzWith Λ f} :=
    (isClosed_setOfPred_lipschitzWith Λ).preimage hcoe
  have hf (x : G) : Continuous (fun p : C(G, G) × C(G, G) => p.1 x) :=
    (continuous_eval_const x).comp continuous_fst
  have hr (x : G) : Continuous (fun p : C(G, G) × C(G, G) => p.2 x) :=
    (continuous_eval_const x).comp continuous_snd
  have hfr (x : G) : Continuous (fun p : C(G, G) × C(G, G) => p.2 (p.1 x)) :=
    continuous_eval.comp (continuous_snd.prodMk (hf x))
  have hrf (x : G) : Continuous (fun p : C(G, G) × C(G, G) => p.1 (p.2 x)) :=
    continuous_eval.comp (continuous_fst.prodMk (hr x))
  simp only [LipschitzPairBounds, Set.ofPred_and, Set.ofPred_forall]
  exact (hl.preimage continuous_fst).inter ((hl.preimage continuous_snd).inter
    ((isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const ((hf x).dist (hf y))).inter
    ((isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const ((hr x).dist (hr y))).inter
    ((isClosed_iInter fun x => isClosed_le ((hfr x).dist continuous_const) continuous_const).inter
      (isClosed_iInter fun x => isClosed_le ((hrf x).dist continuous_const) continuous_const)))))

theorem isClosed_normalizedPairs (Λ : ℝ≥0) : IsClosed (normalizedPairs G Λ) :=
  (isClosed_lipschitzPairBounds G Λ).inter
    (isClosed_eq ((continuous_eval_const 1).comp continuous_fst) continuous_const)

/-- Both maps are anchored on the normalized section: the inverse anchor
bound follows from its quasi-inverse bound and the forward normalization. -/
theorem isCompact_normalizedPairs (Λ : ℝ≥0) : IsCompact (normalizedPairs G Λ) := by
  apply ((isCompact_lipschitz_family Λ (1 : G) 1 Λ).prod
    (isCompact_lipschitz_family Λ (1 : G) 1 Λ)).of_isClosed_subset
      (isClosed_normalizedPairs G Λ)
  intro p hp
  refine ⟨⟨hp.1.1, ?_⟩, ⟨hp.1.2.1, ?_⟩⟩
  · simp [hp.2]
  · simpa only [hp.2] using hp.1.2.2.2.2.1 1

instance instCompactSpaceElemProdContinuousMapNormalizedPair (Λ : ℝ≥0) : CompactSpace (NormalizedPair G Λ) :=
  isCompact_iff_compactSpace.mp (isCompact_normalizedPairs G Λ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# The normalized translation action on pairs

For a pair `(F,B)`, normalization of domain translation by `x` has forward
map `F(x)⁻¹ F(xz)` and inverse map `x⁻¹ B(F(x)z)`. These are actual maps,
with all Lipschitz and quasi-inverse bounds retained. Inverting the parameter
converts the manuscript's right action into a left action.
-/

noncomputable section

open scoped NNReal

namespace PolycyclicRecognition

open MeasureTheory

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

/-- Every pair satisfying the actual coarse bounds has a normalized representative. -/
def normalizePair {Λ : ℝ≥0} (p : C(G, G) × C(G, G))
    (hp : LipschitzPairBounds G Λ p) : NormalizedPair G Λ :=
  ⟨translatePair 1 p, translatePair_bounds_of_bounds Λ p hp 1⟩

omit [IsIsometricSMul G G] in
theorem continuous_translatePair :
    Continuous (fun q : G × (C(G, G) × C(G, G)) => translatePair q.1 q.2) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (G × (C(G, G) × C(G, G))) × G =>
      (q.1.2.1 q.1.1)⁻¹ * q.1.2.1 (q.1.1 * q.2))
    fun_prop
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (G × (C(G, G) × C(G, G))) × G =>
      q.1.1⁻¹ * q.1.2.2 (q.1.2.1 q.1.1 * q.2))
    fun_prop

instance normalizedPairContinuousAction (Λ : ℝ≥0) :
    ContinuousSMul G (NormalizedPair G Λ) where
  continuous_smul := by
    apply Continuous.subtype_mk
    exact continuous_translatePair.comp
      (continuous_fst.inv.prodMk continuous_snd.subtype_val)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairCharts
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# The two product charts of the space of quasi-inverse pairs

Target normalization gives `G × X`; inverse normalization gives `X × G`,
where the latter copy of `X` represents inverse maps. Their transition is
an actual homeomorphism. This is the geometric coordinate change used for
the inverse-coupling measure, before any disintegration or fiber averaging.
-/

noncomputable section

open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

omit [ProperSpace G] in
theorem targetTranslatePair_bounds (z : G) (p : CoarsePair G Λ) :
    LipschitzPairBounds G Λ (targetTranslatePair z p.val) := by
  obtain ⟨hF, hB, hlF, hlB, hBF, hFB⟩ := p.property
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro t u
    change dist (z * p.val.1 t) (z * p.val.1 u) ≤ _
    simpa only [dist_mul_left] using hF.dist_le_mul t u
  · apply LipschitzWith.of_dist_le_mul
    intro t u
    change dist (p.val.2 (z⁻¹ * t)) (p.val.2 (z⁻¹ * u)) ≤ _
    simpa only [dist_mul_left] using hB.dist_le_mul (z⁻¹ * t) (z⁻¹ * u)
  · intro t u
    change _ ≤ dist (z * p.val.1 t) (z * p.val.1 u)
    simpa only [dist_mul_left] using hlF t u
  · intro t u
    change _ ≤ dist (p.val.2 (z⁻¹ * t)) (p.val.2 (z⁻¹ * u))
    simpa only [dist_mul_left] using hlB (z⁻¹ * t) (z⁻¹ * u)
  · intro t
    change dist (p.val.2 (z⁻¹ * (z * p.val.1 t))) t ≤ Λ
    simpa only [inv_mul_cancel_left] using hBF t
  · intro t
    change dist (z * p.val.1 (p.val.2 (z⁻¹ * t))) t ≤ Λ
    rw [← dist_mul_left z⁻¹]
    simpa only [inv_mul_cancel_left] using hFB (z⁻¹ * t)

def targetTranslate (z : G) (p : CoarsePair G Λ) : CoarsePair G Λ :=
  ⟨targetTranslatePair z p.val, targetTranslatePair_bounds z p⟩

/-- Swapping the two maps preserves all six bounds. -/
def swapCoarsePair : CoarsePair G Λ ≃ₜ CoarsePair G Λ where
  toFun p := ⟨p.val.swap, p.property.2.1, p.property.1,
    p.property.2.2.2.1, p.property.2.2.1, p.property.2.2.2.2.2, p.property.2.2.2.2.1⟩
  invFun p := ⟨p.val.swap, p.property.2.1, p.property.1,
    p.property.2.2.2.1, p.property.2.2.1, p.property.2.2.2.2.2, p.property.2.2.2.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _
  continuous_invFun := (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _

/-- The first global product chart is target translation of a normalized pair. -/
def pairTargetChart : (G × NormalizedPair G Λ) ≃ₜ CoarsePair G Λ where
  toFun q := targetTranslate q.1 ⟨q.2.val, q.2.property.1⟩
  invFun p := (p.val.1 1, normalizePair p.val p.property)
  left_inv q := by
    apply Prod.ext
    · change q.1 * q.2.val.1 1 = q.1
      rw [q.2.property.2, mul_one]
    · apply Subtype.ext
      apply Prod.ext <;> apply ContinuousMap.ext <;> intro t <;>
        simp [targetTranslate, targetTranslatePair, normalizePair, translatePair, q.2.property.2]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro t <;>
      simp [targetTranslate, targetTranslatePair, normalizePair, translatePair]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_targetTranslatePair.comp
      (continuous_fst.prodMk continuous_snd.subtype_val)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact (continuous_eval_const 1).comp continuous_subtype_val.fst
    · apply Continuous.subtype_mk
      exact continuous_translatePair.comp (continuous_const.prodMk continuous_subtype_val)

/-- The second product chart parametrizes inverse-normalized pairs. It is
obtained by swapping maps, with the inverse on the group coordinate. -/
def pairSourceChart : (NormalizedPair G Λ × G) ≃ₜ CoarsePair G Λ :=
  ((Homeomorph.prodComm _ _).trans
    ((Homeomorph.inv G).prodCongr (Homeomorph.refl _))).trans
      (pairTargetChart.trans swapCoarsePair)

/-- The exact coordinate change underlying the inverse coupling. -/
def pairChartTransition : (G × NormalizedPair G Λ) ≃ₜ (NormalizedPair G Λ × G) :=
  pairTargetChart.trans pairSourceChart.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairCoupling
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation invariance of the pair coupling

The two commuting translations are written in both product charts. Haar
measure times the stationary probability gives the actual invariant coupling.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

variable [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- The coupling measure in inverse coordinates, defined by the actual chart. -/
def inversePairCoupling (m : Measure G) (μ : Measure (NormalizedPair G Λ)) :
    Measure (NormalizedPair G Λ × G) :=
  (m.prod μ).map pairChartTransition

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InverseSection
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The invariant measure on the inverse section

For the actual compact space of quasi-inverse pairs, the Haar coupling in
inverse coordinates factors as a finite nonzero invariant section measure
times Haar measure. No absolute continuity of the section measure is used.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

instance inversePairCoupling_finiteOnCompacts
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts (inversePairCoupling m μ) :=
  Measure.IsFiniteMeasureOnCompacts.map (m.prod μ) pairChartTransition

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationaryCentered
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The zero-mean Hilbert representation and stationary sublinearity

The closed kernel of integration is invariant under inverse pullback.
Ergodicity removes its invariant vectors. This constructs the representation
to which the published reduced-cohomology input is applied; the conclusion
is the manuscript's averaged sublinear estimate for a fixed measure.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

attribute [local instance] stationaryL2Action

/-- Restrict the pullback representation to the kernel of integration. -/
@[instance_reducible]
def zeroMeanL2Action : DistribMulAction G (ZeroMeanL2 (W := W) μ) where
  smul g v := ⟨stationaryPullback μ g v.val, by
    change stationaryL2Mean μ (stationaryPullback μ g v.val) = 0
    rw [stationaryL2Mean_pullback]
    exact v.property⟩
  one_smul v := Subtype.ext (stationaryPullback_one (W := W) μ v.val)
  mul_smul g h v := Subtype.ext (stationaryPullback_mul (W := W) μ g h v.val)
  smul_zero g := Subtype.ext ((stationaryPullback (W := W) μ g).map_zero)
  smul_add g v w := Subtype.ext ((stationaryPullback (W := W) μ g).map_add v.val w.val)

attribute [local instance] zeroMeanL2Action

/-- Averaging any `L²` cocycle gives a genuine height homomorphism. -/
def l2MeanSlope (b : G → Lp W 2 μ) (hb : IsCocycle b) : G →* Multiplicative W where
  toFun g := Multiplicative.ofAdd (stationaryL2Mean μ (b g))
  map_one' := by simp only [hb.map_one, map_zero]; rfl
  map_mul' g h := by
    apply Multiplicative.ext
    change stationaryL2Mean μ (b (g * h)) = _
    rw [hb g h, map_add]
    congr 1
    exact stationaryL2Mean_pullback μ g (b h)

/-- Subtracting the actual averaged slope produces a zero-mean cocycle. -/
def centeredL2Cocycle (b : G → Lp W 2 μ) (g : G) : ZeroMeanL2 (W := W) μ :=
  ⟨b g - Lp.const 2 μ (stationaryL2Mean μ (b g)), by
    change stationaryL2Mean μ (_ - _) = 0
    rw [map_sub, stationaryL2Mean_const, sub_self]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PairHeightCocycle
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Height evaluation on the compact pair space

The normalized action makes evaluation of a continuous height homomorphism
an actual continuous `L²` cocycle. The stationary slope estimate therefore
applies to this concrete cocycle.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Λ : ℝ≥0}

/-- Height evaluation of the forward map of a normalized pair. -/
def pairHeight (π : G →* Multiplicative W) (g : G) (p : NormalizedPair G Λ) : W :=
  (π (p.val.1 g)).toAdd

omit [NormedSpace ℝ W] [ProperSpace G] in
theorem pairHeight_cocycle (π : G →* Multiplicative W) (g h : G)
    (p : NormalizedPair G Λ) :
    pairHeight π (g * h) p = pairHeight π g p + pairHeight π h (g⁻¹ • p) := by
  unfold pairHeight
  rw [normalizedPair_smul_fst, inv_inv, map_mul π, map_inv π]
  simp only [toAdd_mul, toAdd_inv]
  abel

omit [NormedSpace ℝ W] [IsIsometricSMul G G] [IsTopologicalGroup G] in
theorem continuous_pairHeight (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) :
    Continuous (fun q : G × NormalizedPair G Λ => pairHeight π q.1 q.2) := by
  exact hπ.comp (continuous_eval.comp
    ((continuous_fst.comp continuous_subtype_val).comp continuous_snd |>.prodMk continuous_fst))

/-- The continuous height profile at a fixed group element. -/
def pairHeightProfile (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (g : G) : C(NormalizedPair G Λ, W) :=
  ⟨pairHeight π g, (continuous_pairHeight π hπ).comp
    (continuous_const.prodMk continuous_id)⟩

variable [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]

/-- The `L²` class of height evaluation, using the canonical continuous-map inclusion. -/
def pairHeightL2 (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (g : G) : Lp W 2 μ :=
  ContinuousMap.toLp 2 μ ℝ (pairHeightProfile π hπ g)

attribute [local instance] stationaryL2Action
attribute [local instance] zeroMeanL2Action

theorem isCocycle_pairHeightL2 [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd) :
    IsCocycle (pairHeightL2 μ π hπ) := by
  intro g h
  apply Lp.ext
  have hc (k : G) : pairHeightL2 μ π hπ k =ᵐ[μ] pairHeight π k :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ k)
  have hh := (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving.ae_eq_comp (hc h)
  have hpull : stationaryPullback μ g (pairHeightL2 μ π hπ h) =ᵐ[μ]
      fun p => pairHeightL2 μ π hπ h (g⁻¹ • p) :=
    Lp.coeFn_compMeasurePreserving (pairHeightL2 μ π hπ h)
      (measurePreserving_smul g⁻¹ μ)
  filter_upwards [hc (g * h), hc g, hh,
    Lp.coeFn_add (pairHeightL2 μ π hπ g) (g • pairHeightL2 μ π hπ h),
    hpull] with p hgh hg hh hadd hpull
  simp only [Pi.add_apply, Function.comp_apply] at hadd hpull hh
  rw [hgh, hadd, hg]
  change pairHeight π (g * h) p = pairHeight π g p +
    (stationaryPullback μ g (pairHeightL2 μ π hπ h)) p
  rw [hpull, hh]
  exact pairHeight_cocycle π g h p

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CouplingTransfer
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer functions in the two coupling charts

The transfer is lifted by adding target height. Its domain defect is the
original stationary cocycle defect. In inverse coordinates, differences
inside a fiber are the same defects, and fiber averaging gives the exact
inverse transfer identity.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [NormedAddCommGroup W]

/-- Extend a section transfer by target-height equivariance. -/
def pairTransferLift (π : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (q : G × NormalizedPair G Λ) : W :=
  (π q.1).toAdd + φ q.2

/-- In inverse coordinates, subtract the proposed domain height. -/
def inverseFiberTransfer (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (q : NormalizedPair G Λ × G) : W :=
  pairTransferLift π φ (pairChartTransition.symm q) - (l q.2).toAdd

variable [MeasurableSpace G] [NormedSpace ℝ W] [CompleteSpace W]

/-- Average the transfer over a whole probability fiber. -/
def inverseAveragedTransfer (β : Measure G) (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (p : NormalizedPair G Λ) : W :=
  ∫ x, inverseFiberTransfer π l φ (p, x) ∂β

/-- The error is the average of differences inside one fiber. -/
def inverseAverageError (β : Measure G) (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (y : G) (p : NormalizedPair G Λ) : W :=
  ∫ x, inverseFiberTransfer π l φ (p, p.val.1 y * x) -
    inverseFiberTransfer π l φ (p, x) ∂β

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinTranslations
attribute [-instance] _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instGroup _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp_mul _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp_neg _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual inverse of a coordinate right translation -/

noncomputable section

namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The finite group laws give a homeomorphism, with inverse translation
parameter `-q`. This identifies the inverse used by sampling densities. -/
def dynkinRightTranslation {c : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (h : PolynomialGroupLaws (dynkinProduct a B))
    (q : V) : V ≃ₜ V where
  toFun x := dynkinProduct a B x q
  invFun x := dynkinProduct a B x (-q)
  left_inv x := by
    change dynkinProduct a B (dynkinProduct a B x q) (-q) = x
    rw [h.1]
    have hq : dynkinProduct a B q (-q) = 0 := by
      simpa only [neg_neg] using h.2.2.2.1 (-q)
    rw [hq, h.2.2.1]
  right_inv x := by
    change dynkinProduct a B (dynkinProduct a B x (-q)) q = x
    rw [h.1, h.2.2.2.1, h.2.2.1]
  continuous_toFun := continuous_dynkinProduct a _ _ _
    continuous_const continuous_id continuous_const
  continuous_invFun := continuous_dynkinProduct a _ _ _
    continuous_const continuous_id continuous_const

@[simp] theorem dynkinRightTranslation_apply {c : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (h : PolynomialGroupLaws (dynkinProduct a B))
    (q x : V) : dynkinRightTranslation a B h q x = dynkinProduct a B x q := rfl

@[simp] theorem dynkinRightTranslation_symm_apply {c : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (h : PolynomialGroupLaws (dynkinProduct a B))
    (q x : V) : (dynkinRightTranslation a B h q).symm x =
      dynkinProduct a B x (-q) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_EnvelopingTruncation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite word truncation of an enveloping algebra

The ideal is generated by all sufficiently long products of Lie generators.
It is invariant under every extended Lie derivation.
-/

noncomputable section
namespace PolycyclicRecognition

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "η" => UniversalEnvelopingAlgebra.ι R (L := L)

theorem longWord_mem_envelopingTruncationIdeal (c : ℕ) (l : List L)
    (hl : c ≤ l.length) : (l.map η).prod ∈ envelopingTruncationIdeal (R := R) c :=
  TwoSidedIdeal.subset_span ⟨l, hl, rfl⟩

theorem word_derivation_mem_truncation (D : LieDerivation R L L) (c : ℕ)
    (p l : List L) (h : c ≤ p.length + l.length) :
    (p.map η).prod * envelopingDerivation D (l.map η).prod ∈
      envelopingTruncationIdeal (R := R) c := by
  induction l generalizing p with
  | nil =>
    have hzero : envelopingDerivation D (1 : U) = 0 := by
      simpa using envelopingDerivation_scalar D (1 : R)
    simpa only [List.map_nil, List.prod_nil, hzero, mul_zero] using
      (envelopingTruncationIdeal (R := R) (L := L) c).zero_mem
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, envelopingDerivation_mul,
      envelopingDerivation_generator, mul_add]
    apply TwoSidedIdeal.add_mem
    · have hp : c ≤ (p ++ [x]).length + l.length := by
        simpa only [List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, zero_add, Nat.add_assoc, Nat.add_comm 1] using h
      simpa only [List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, mul_assoc] using ih (p ++ [x]) hp
    · have hp : c ≤ (p ++ D x :: l).length := by
        simpa only [List.length_append, List.length_cons] using h
      simpa only [List.map_append, List.prod_append, List.map_cons,
        List.prod_cons] using longWord_mem_envelopingTruncationIdeal c (p ++ D x :: l) hp

theorem envelopingDerivation_preserves_truncation (D : LieDerivation R L L)
    (c : ℕ) {u : U} (hu : u ∈ envelopingTruncationIdeal (R := R) c) :
    envelopingDerivation D u ∈ envelopingTruncationIdeal (R := R) c := by
  induction hu using TwoSidedIdeal.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    simpa using word_derivation_mem_truncation D c [] l (by simpa using hl)
  | zero => simpa only [map_zero] using (envelopingTruncationIdeal (R := R) (L := L) c).zero_mem
  | add a b _ _ ha hb =>
    rw [map_add]
    exact TwoSidedIdeal.add_mem _ ha hb
  | neg a _ ha =>
    rw [map_neg]
    exact TwoSidedIdeal.neg_mem _ ha
  | left_absorb a b hb hDb =>
    rw [envelopingDerivation_mul]
    exact TwoSidedIdeal.add_mem _
      (TwoSidedIdeal.mul_mem_left _ _ _ hDb)
      (TwoSidedIdeal.mul_mem_left _ _ _ hb)
  | right_absorb b a ha hDa =>
    rw [envelopingDerivation_mul]
    exact TwoSidedIdeal.add_mem _
      (TwoSidedIdeal.mul_mem_right _ _ _ ha)
      (TwoSidedIdeal.mul_mem_right _ _ _ hDa)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorExtensionTopology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing the kernel while retaining the discrete quotient -/

noncomputable section
namespace PolycyclicRecognition
open Filter Topology

variable {N Q : Type*} [Group N] [Group Q] [TopologicalSpace N] [TopologicalSpace Q]
  (S : NonabelianFactorSystem N Q)

attribute [local instance] factorExtensionTopology

def factorExtensionHomeomorph : FactorExtension S ≃ₜ N × Q where
  toEquiv := FactorExtension.equivProd S
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_id

instance instT2SpaceFactorExtension [T2Space N] [T2Space Q] : T2Space (FactorExtension S) :=
  (factorExtensionHomeomorph S).isEmbedding.t2Space

instance instLocallyCompactSpaceFactorExtension [LocallyCompactSpace N] [LocallyCompactSpace Q] :
    LocallyCompactSpace (FactorExtension S) :=
  (factorExtensionHomeomorph S).locallyCompactSpace_iff.mpr inferInstance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorSystemSymmetrySubgroup
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Automorphisms commuting with the section actions and fixing its factors -/

namespace PolycyclicRecognition
variable {N Q : Type} [Group N] [Group Q]

def factorSystemSymmetries (R : NonabelianFactorSystem N Q) : Subgroup (MulAut N) where
  carrier := {A | (∀ q, Commute A (R.action q)) ∧ ∀ q r, A (R.factor q r) = R.factor q r}
  one_mem' := ⟨fun _ => Commute.one_left _, fun _ _ => rfl⟩
  mul_mem' := by
    intro A B hA hB
    refine ⟨fun q => (hA.1 q).mul_left (hB.1 q), ?_⟩
    intro q r
    change A (B (R.factor q r)) = R.factor q r
    rw [hB.2, hA.2]
  inv_mem' := by
    intro A hA
    refine ⟨fun q => (hA.1 q).inv_left, ?_⟩
    intro q r
    apply A.injective
    change A (A.symm (R.factor q r)) = A (R.factor q r)
    rw [A.apply_symm_apply, hA.2]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FilteredNilpotentPerturbation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent perturbations along a finite filtration

An operator which agrees with a nilpotent operator on each successive
quotient is nilpotent. No commutation of the two operators is required.
-/

namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem nilpotent_of_filtered_nilpotent_perturbation
    (F : ℕ → Submodule ℝ V) (hzero : F 0 = ⊤) {c : ℕ} (hc : F c = ⊥)
    (a b : Module.End ℝ V)
    (ha : ∀ k x, x ∈ F k → a x ∈ F k)
    (hb : ∀ k x, x ∈ F k → b x ∈ F k)
    (hdiff : ∀ k x, x ∈ F k → (a - b) x ∈ F (k + 1))
    (hbn : IsNilpotent b) : IsNilpotent a := by
  have hbp (n k : ℕ) (x : V) (hx : x ∈ F k) : (b ^ n) x ∈ F k := by
    induction n with
    | zero => exact hx
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hb k _ ih
  have hp (n k : ℕ) (x : V) (hx : x ∈ F k) :
      (a ^ n) x - (b ^ n) x ∈ F (k + 1) := by
    induction n with
    | zero => simp only [pow_zero, Module.End.one_apply, sub_self, Submodule.zero_mem]
    | succ n ih =>
      have hh := (F (k + 1)).add_mem (ha (k + 1) _ ih) (hdiff k _ (hbp n k x hx))
      convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, map_sub]; abel)
  obtain ⟨m, hm⟩ := hbn
  have hraise (k : ℕ) (x : V) (hx : x ∈ F k) : (a ^ m) x ∈ F (k + 1) := by
    simpa only [hm, LinearMap.zero_apply, sub_zero] using hp m k x hx
  obtain ⟨n, hn⟩ := nilpotent_of_raises_finite_filtration F hzero hc (a ^ m) hraise
  exact ⟨m * n, by rwa [pow_mul]⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubgroupInductionCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct-sum coordinates for induction from an arbitrary subgroup

Right cosets, with a chosen representative, are sufficient. No normality of
the subgroup is required for exact induction or for the rational base case.
-/
noncomputable section
namespace PolycyclicRecognition
open Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (H : Subgroup G)

variable (k : Type) [CommRing k] (A : Rep k H)

def subgroupInductionCoordinatesInv : (subgroupRightCosets H →₀ A) →ₗ[k] Rep.ind H.subtype A :=
  Finsupp.lsum k fun c => IndV.mk H.subtype A.ρ (subgroupRightRepresentative H c)

@[simp]
theorem subgroupInductionCoordinatesInv_single (c : subgroupRightCosets H) (a : A) :
    subgroupInductionCoordinatesInv H k A (Finsupp.single c a) =
      IndV.mk H.subtype A.ρ (subgroupRightRepresentative H c) a := by
  simp [subgroupInductionCoordinatesInv]

theorem subgroupInductionCoordinates_right_inv :
    (subgroupInductionCoordinates H k A).comp (subgroupInductionCoordinatesInv H k A) =
      LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro c
  apply LinearMap.ext
  intro a
  change subgroupInductionCoordinates H k A
    (subgroupInductionCoordinatesInv H k A (Finsupp.single c a)) = _
  rw [subgroupInductionCoordinatesInv_single, subgroupInductionCoordinates_mk,
    subgroupRightRepresentative_coset, subgroupRightPart_representative]
  simp

theorem subgroupInductionCoordinates_left_inv :
    (subgroupInductionCoordinatesInv H k A).comp (subgroupInductionCoordinates H k A) =
      LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change subgroupInductionCoordinatesInv H k A
    (subgroupInductionCoordinates H k A (IndV.mk H.subtype A.ρ g a)) = IndV.mk H.subtype A.ρ g a
  rw [subgroupInductionCoordinates_mk, subgroupInductionCoordinatesInv_single]
  change Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp H.subtype) A.ρ)
    (MonoidAlgebra.single (subgroupRightRepresentative H (subgroupRightCoset H g)) (1 : k) ⊗ₜ[k]
      A.ρ (subgroupRightPart H g)⁻¹ a) =
    Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp H.subtype) A.ρ)
      (MonoidAlgebra.single g (1 : k) ⊗ₜ[k] a)
  rw [Coinvariants.mk_tmul_inv]
  simp only [MonoidHom.comp_apply, Representation.leftRegular, Representation.ofMulAction_single,
    Subgroup.subtype_apply, smul_eq_mul, subgroupRightPart_decompose]

def subgroupInductionEquiv : Rep.ind H.subtype A ≃ₗ[k] (subgroupRightCosets H →₀ A) :=
  LinearEquiv.ofLinearMap (subgroupInductionCoordinates H k A) (subgroupInductionCoordinatesInv H k A)
    (subgroupInductionCoordinates_right_inv H k A) (subgroupInductionCoordinates_left_inv H k A)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteIndexTraceRetract
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative trace-one coefficients are retracts of induced restrictions

The averaging is over a finite coset space, so the subgroup itself may be
infinite. The trace element is invariant under that subgroup.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G R : Type} [Group G] [Ring R] [MulSemiringAction G R]
variable (N : Subgroup G)

/-- Right multiplication is well-defined on right cosets without normality. -/
def subgroupRightCosetMulEquiv (g : G) : subgroupRightCosets N ≃ subgroupRightCosets N where
  toFun := Quotient.map (fun x => x * g) (by
    intro x y h
    apply (QuotientGroup.rightRel_apply).mpr
    simpa [mul_inv_rev, mul_assoc] using (QuotientGroup.rightRel_apply).mp h)
  invFun := Quotient.map (fun x => x * g⁻¹) (by
    intro x y h
    apply (QuotientGroup.rightRel_apply).mpr
    simpa [mul_inv_rev, mul_assoc] using (QuotientGroup.rightRel_apply).mp h)
  left_inv c := by induction c using Quotient.inductionOn; simp [mul_assoc]
  right_inv c := by induction c using Quotient.inductionOn; simp [mul_assoc]

@[simp]
theorem subgroupRightCosetMulEquiv_mk (g x : G) :
    subgroupRightCosetMulEquiv N g (subgroupRightCoset N x) =
      subgroupRightCoset N (x * g) := rfl

theorem induced_mk_mul_left (A : Rep.{0} ℤ N) (n : N) (g : G) (a : A) :
    IndV.mk N.subtype A.ρ ((n : G) * g) (A.ρ n a) = IndV.mk N.subtype A.ρ g a := by
  apply (subgroupInductionEquiv N ℤ A).injective
  change subgroupInductionCoordinates N ℤ A _ = subgroupInductionCoordinates N ℤ A _
  rw [subgroupInductionCoordinates_mk, subgroupInductionCoordinates_mk,
    subgroupRightCoset_mul, subgroupRightPart_mul]
  simp [mul_inv_rev, map_mul, Module.End.mul_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexifiedOperatorExponential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponentials commute with the concrete complexification of operators -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable (L : Type) [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance instComplexNormedLieAlgebraTensorProductRealComplex : ComplexNormedLieAlgebra (ℂ ⊗[ℝ] L) := complexificationNormedLie L

def continuousComplexifiedEnd :
    (L →L[ℝ] L) →ₐ[ℝ] ((ℂ ⊗[ℝ] L) →L[ℂ] (ℂ ⊗[ℝ] L)) :=
  ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℂ ⊗[ℝ] L)).restrictScalars ℝ).toAlgHom.comp
    ((Module.End.baseChangeHom ℝ ℂ L).comp
      (Module.End.toContinuousLinearMap (𝕜 := ℝ) L).symm.toAlgHom)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentLinearFlow
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial linear flows used in the logarithm of a lattice automorphism -/

noncomputable section
namespace PolycyclicRecognition

section Algebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

attribute [local instance] OAI.PolycyclicRecognition.linearFlowRationalModule
theorem nilpotentLinearFlow_add (D : Module.End ℝ V) (hD : IsNilpotent D) (s t : ℝ) :
    nilpotentLinearFlow D (s + t) = nilpotentLinearFlow D s * nilpotentLinearFlow D t := by
  have hc : Commute (s • D) (t • D) := by
    change (s • D) * (t • D) = (t • D) * (s • D)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm s t]
  change IsNilpotent.exp ((s + t) • D) = IsNilpotent.exp (s • D) * IsNilpotent.exp (t • D)
  rw [add_smul]
  exact IsNilpotent.exp_add_of_commute hc (hD.smul s) (hD.smul t)

theorem nilpotentLinearFlow_nat (D : Module.End ℝ V) (hD : IsNilpotent D) (n : ℕ) :
    nilpotentLinearFlow D (n : ℝ) = IsNilpotent.exp D ^ n := by
  induction n with
  | zero => simp [nilpotentLinearFlow]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, nilpotentLinearFlow_add D hD, ih, pow_succ]
    simp only [nilpotentLinearFlow, one_smul]

theorem coordinatePolynomial_nilpotentLinearFlow {d : ℕ}
    (b : Module.Basis (Fin d) ℝ V) (D : Module.End ℝ V) (hD : IsNilpotent D) (x : V) :
    IsCoordinatePolynomial (fun t : Fin 1 → ℝ => b.equivFun (nilpotentLinearFlow D (t 0) x)) := by
  obtain ⟨k, hk⟩ := hD
  refine ⟨fun j => ∑ i ∈ Finset.range k,
    MvPolynomial.X 0 ^ i * MvPolynomial.C (b.equivFun (((i.factorial : ℚ)⁻¹ • D ^ i) x) j), ?_⟩
  intro t j
  change MvPolynomial.eval t _ = b.equivFun (nilpotentLinearFlow D (t 0) x) j
  rw [nilpotentLinearFlow_eq_sum D hk]
  simp only [map_sum, map_smul, MvPolynomial.eval_X, MvPolynomial.eval_C, map_mul,
    map_pow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end Algebra

section Derivative
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

attribute [local instance] OAI.PolycyclicRecognition.linearFlowDerivativeRationalModule
theorem hasDerivAt_nilpotentLinearFlow_zero (D : Module.End ℝ V) (hD : IsNilpotent D)
    (x : V) : HasDerivAt (fun t : ℝ => nilpotentLinearFlow D t x) (D x) 0 := by
  obtain ⟨k, hk⟩ := hD
  have hk' : D ^ (k + 2) = 0 := by rw [pow_add, hk, zero_mul]
  have hterm (i : ℕ) :
      HasDerivAt (fun t : ℝ => t ^ i • (((i.factorial : ℚ)⁻¹ • D ^ i) x))
        (if i = 1 then D x else 0) 0 := by
    have hh : HasDerivAt
        (fun t : ℝ => t ^ i • (((i.factorial : ℚ)⁻¹ • D ^ i) x))
        (((i : ℝ) * 0 ^ (i - 1)) • (((i.factorial : ℚ)⁻¹ • D ^ i) x)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow i).smul_const
        (((i.factorial : ℚ)⁻¹ • D ^ i) x)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    by_cases hi : i = 1
    · subst i
      simp
    · by_cases hz : i = 0
      · subst i
        simp
      · have hsub : i - 1 ≠ 0 := by omega
        simp [hi, zero_pow hsub]
  have hsum := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.range (k + 2)) => hterm i)
  have heq : (fun t : ℝ => nilpotentLinearFlow D t x) =
      (fun t => ∑ i ∈ Finset.range (k + 2),
        t ^ i • (((i.factorial : ℚ)⁻¹ • D ^ i) x)) :=
    funext (fun t => nilpotentLinearFlow_eq_sum D hk' t x)
  rw [heq]
  simpa using hsum

end Derivative
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UnipotentLieLogarithm
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithm of a unipotent Lie automorphism is a derivation

Integer iterates preserve the bracket. Polynomiality extends that identity to
the real flow; its derivative at zero is the derivation identity.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance unipotentLogRationalModule : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

theorem nilpotentLinearFlow_preserves_lie
    (A : L ≃ₗ⁅ℝ⁆ L) (D : Module.End ℝ L) (hD : IsNilpotent D)
    (hExp : IsNilpotent.exp D = A.toLinearMap) (t : ℝ) (x y : L) :
    nilpotentLinearFlow D t ⁅x, y⁆ = ⁅nilpotentLinearFlow D t x, nilpotentLinearFlow D t y⁆ := by
  let b := Module.finBasis ℝ L
  have hB (u v : L) : basisBracketLinear b (b.equivFun u) (b.equivFun v) =
      b.equivFun ⁅u, v⁆ := by
    change b.equivFun ⁅b.equivFun.symm (b.equivFun u), b.equivFun.symm (b.equivFun v)⁆ = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hl := coordinatePolynomial_nilpotentLinearFlow b D hD ⁅x, y⁆
  have hr := IsCoordinatePolynomial.bilinear (basisBracketLinear b)
    (coordinatePolynomial_nilpotentLinearFlow b D hD x)
    (coordinatePolynomial_nilpotentLinearFlow b D hD y)
  have hp (n : ℕ) (u v : L) :
      (A.toLinearMap ^ n) ⁅u, v⁆ = ⁅(A.toLinearMap ^ n) u, (A.toLinearMap ^ n) v⁆ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change A ⁅(A.toLinearMap ^ n) u, (A.toLinearMap ^ n) v⁆ =
        ⁅A ((A.toLinearMap ^ n) u), A ((A.toLinearMap ^ n) v)⁆
      exact A.map_lie _ _
  have he := hl.ext_nat_grid hr (by
    intro z
    change b.equivFun (nilpotentLinearFlow D (z 0 : ℝ) ⁅x, y⁆) =
      basisBracketLinear b (b.equivFun (nilpotentLinearFlow D (z 0 : ℝ) x))
        (b.equivFun (nilpotentLinearFlow D (z 0 : ℝ) y))
    rw [hB]
    simp only [nilpotentLinearFlow_nat D hD, hExp]
    exact congrArg b.equivFun (hp (z 0) x y))
  have ht := congrFun he (fun _ : Fin 1 => t)
  apply b.equivFun.injective
  change b.equivFun (nilpotentLinearFlow D t ⁅x, y⁆) =
    basisBracketLinear b (b.equivFun (nilpotentLinearFlow D t x))
      (b.equivFun (nilpotentLinearFlow D t y)) at ht
  rwa [hB] at ht

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FixedVectorLieLogarithm
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The chosen Lie logarithm vanishes on fixed vectors

The compatible spectral character has value zero at the identity. This
retains the quotient directions when extending the integral nilshadow action.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct

section Real
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance fixedVectorLogRationalModule : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

end Real
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FixedPowerLogarithms
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Commuting real logarithms retaining the fixed directions -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance fixedPowerLogRationalModule : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorOrbit
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spanning by conjugated generator directions

Products of adjoint exponentials applied to a Lie-generating family span the
whole algebra. This proves the linear nondegeneracy needed to construct a
submersive generator product scheme; it does not assume controllability or a
volume estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.generatorOrbitNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.generatorOrbitNormedSpace
/-- The linear span of all conjugated generator directions. -/
def generatorOrbitSpan (X : I → L) : Submodule ℝ L :=
  Submodule.span ℝ (Set.range (fun p : List (I × ℝ) × I =>
    generatorAdjointWord X p.1 (X p.2)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordBasis
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A homogeneous bracket-word basis of the Cartan ideal

This supplies actual nonzero-root letters and strictly positive integral
letter multiplicities for the nilpotent box data.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
def cartanGeneratorPool : Set (cartanRootIdeal H) :=
  {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ (v : L) ∈ rootSpace H χ}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SwitchParameterPullback
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling the successful event back to the original independent samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

/-- Apply the prescribed sampling map in each of the two independent slots. -/
def mapSwitchParameters {A B : Type*} (f : ℕ → A → B) :
    (n k : ℕ) → SwitchParameters A k → SwitchParameters B k
  | _, 0, _ => PUnit.unit
  | n, k + 1, p => (f n p.1, f n p.2.1, mapSwitchParameters f (n + 1) k p.2.2)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_VectorSwitchParameters
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite vectors of independent pairs and the recursive switch law -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

def vectorSwitchParameters {A : Type*} :
    (k : ℕ) → (Fin k → A × A) → SwitchParameters A k
  | 0, _ => PUnit.unit
  | k + 1, p => ((p 0).1, (p 0).2, vectorSwitchParameters k (fun i => p i.succ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FlatSwitchSamples
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive independent sampling law on the flat parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

def flatSwitchSamples (m : ℕ) (t : Fin (m + m) → ℝ) : SwitchParameters ℝ m :=
  vectorSwitchParameters m (flatSamplePairs m t)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GoodFiniteWordVertices
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual good vertices of a successful finite block -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G]

@[simp] theorem finiteWordVertex_zero {m : ℕ} (x : G) (u : Fin m → G) :
    finiteWordVertex x u 0 = x := by
  simp only [finiteWordVertex, Fin.val_zero, List.take_zero, List.prod_nil, mul_one]

@[simp] theorem finiteWordVertex_last {m : ℕ} (x : G) (u : Fin m → G) :
    finiteWordVertex x u (Fin.last m) = x * (List.ofFn u).prod := by
  simp only [finiteWordVertex, Fin.val_last, List.take_of_length_le (by simp :
    (List.ofFn u).length ≤ m)]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GradedCoordinateLimit
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The limiting Lie law of maximizing word coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped BigOperators Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

/-- Retain exactly the structure constants which preserve total degree. -/
def gradedCoordinateBracket (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ∑ i, ∑ j, ∑ k, (if cost i + cost j = cost k then b.repr ⁅b i, b j⁆ k else 0) •
    coordinateBilinearUnit i j k

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InductionAmbientQuotient
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common ambient representation for subgroup induction

All the induced restrictions of a fixed coefficient are quotients of the same
module. The relations increase with the subgroup. The commuting right action
on the group-ring factor gives the actual ambient group action.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (A : Rep.{0} ℤ G)

theorem inductionRelations_invariant (H : Subgroup G) :
    RepresentationInvariant (inductionAmbient A)
      (subgroupCoinvariantRelations (inductionDiagonalAction A) H) := by
  intro g x hx
  change inductionAmbientAction A g x ∈
    subgroupCoinvariantRelations (inductionDiagonalAction A) H
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨h, v⟩, rfl⟩ := hx
    change inductionAmbientAction A g ((inductionDiagonalAction A h.val) v - v) ∈
      subgroupCoinvariantRelations (inductionDiagonalAction A) H
    rw [map_sub]
    have he := LinearMap.congr_fun (inductionAmbient_diagonal_commute A g h.val) v
    change inductionAmbientAction A g (inductionDiagonalAction A h.val v) =
      inductionDiagonalAction A h.val (inductionAmbientAction A g v) at he
    rw [he]
    exact Coinvariants.sub_mem_ker
      (ρ := (inductionDiagonalAction A).comp H.subtype) h (inductionAmbientAction A g v)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    change inductionAmbientAction A g (r • x) ∈
      subgroupCoinvariantRelations (inductionDiagonalAction A) H
    rw [map_smul]
    exact Submodule.smul_mem _ r hx

/-- The quotient action is the induction action, including its inverse convention. -/
def inductionAmbientQuotientIso (H : Subgroup G) :
    Rep.quotient (inductionAmbient A)
      (subgroupCoinvariantRelations (inductionDiagonalAction A) H)
      (inductionRelations_invariant A H) ≅ Rep.ind H.subtype (Rep.res H.subtype A) where
  hom := Rep.ofHom ⟨LinearMap.id, fun g => by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl⟩
  inv := Rep.ofHom ⟨LinearMap.id, fun g => by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl⟩
  hom_inv_id := by apply Rep.hom_ext; rfl
  inv_hom_id := by apply Rep.hom_ext; rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InnerBarTranslation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An augmented bar-resolution lift of inner conjugation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Rep Finsupp
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem innerBarFreeMap_d (a : G) (n : ℕ) :
    innerBarFreeMap a (n + 1) ≫ Rep.barComplex.d ℤ G n =
      Rep.barComplex.d ℤ G n ≫ innerBarFreeMap a n := by
  apply Rep.free_ext
  intro x
  change (Rep.barComplex.d ℤ G n).hom
      ((innerBarFreeMap a (n + 1)).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    (innerBarFreeMap a n).hom
      ((Rep.barComplex.d ℤ G n).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [innerBarFreeMap_single, one_mul, bar_d_single_single, Rep.barComplex.d_single,
    map_add, map_sum, innerBarFreeMap_single]
  congr 1
  · congr 1
    simp [MulAut.conj_apply, mul_assoc]
  · apply Finset.sum_congr rfl
    intro j _
    rw [innerBarFreeMap_single, one_mul, one_mul]
    congr 1
    exact (Fin.comp_contractNth (· * ·) (· * ·)
      (f := (MulAut.conj a).toMonoidHom) (map_mul _) j x).symm

def innerBarMap (a : G) : Rep.barComplex ℤ G ⟶ Rep.barComplex ℤ G :=
  ChainComplex.ofHom (innerBarFreeMap a) (fun n => by
    simpa only [ChainComplex.of_d] using innerBarFreeMap_d a n)

theorem innerBarMap_augmentation (a : G) :
    innerBarMap a ≫ (Rep.barResolution ℤ G).π = (Rep.barResolution ℤ G).π := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution ℤ G).π.f 0).hom
        ((innerBarFreeMap a 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
      ((Rep.barResolution ℤ G).π.f 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))
    rw [innerBarFreeMap_single, barResolution_pi_single, barResolution_pi_single]
  | succ i =>
    change (innerBarMap a).f (i + 1) ≫ (0 : (Rep.barComplex ℤ G).X (i + 1) ⟶ _) = 0
    exact CategoryTheory.Limits.comp_zero

def innerBarMapHomotopy (a : G) : Homotopy (innerBarMap a) (𝟙 (Rep.barComplex ℤ G)) := by
  have hid : (Rep.barResolution ℤ G).π ≫
      (ChainComplex.single₀ (Rep ℤ G)).map (𝟙 (Rep.trivial ℤ G ℤ)) =
      (Rep.barResolution ℤ G).π := by
    exact (congrArg (fun f => (Rep.barResolution ℤ G).π ≫ f)
      ((ChainComplex.single₀ (Rep ℤ G)).map_id (Rep.trivial ℤ G ℤ))).trans (Category.comp_id _)
  apply ProjectiveResolution.liftHomotopy (P := Rep.barResolution ℤ G)
    (Q := Rep.barResolution ℤ G) (𝟙 (Rep.trivial ℤ G ℤ))
    (innerBarMap a) (𝟙 (Rep.barComplex ℤ G))
  · exact (innerBarMap_augmentation a).trans hid.symm
  · exact (Category.id_comp (Rep.barResolution ℤ G).π).trans hid.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InvariantFactor
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning on all invariant measurable sets

The factor retains the original points but equips them with the sigma algebra
of invariant sets. Its conditional kernel is pointwise constant on every orbit
and has the original probability as its barycenter.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set

variable (G X : Type*) [Group G] [mX : MeasurableSpace X] [MulAction G X]

instance instMeasurableSpaceInvariantFactor : MeasurableSpace (InvariantFactor G X) :=
  MeasurableSpace.comap InvariantFactor.val (invariantSigma G X)

/-- Identity on points, with the coarser invariant sigma algebra as codomain. -/
def invariantFactorMap (x : X) : InvariantFactor G X := ⟨x⟩

theorem measurable_invariantFactorMap : Measurable (invariantFactorMap G X) := by
  rw [measurable_iff_comap_le]
  change ((invariantSigma G X).comap InvariantFactor.val).comap (invariantFactorMap G X) ≤ _
  rw [MeasurableSpace.comap_comp]
  change (invariantSigma G X).comap id ≤ _
  rw [MeasurableSpace.comap_id]
  exact invariantSigma_le G X

variable {G X}

variable [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Conditional probabilities over the complete invariant sigma algebra. -/
def invariantConditionalKernel : Kernel (InvariantFactor G X) X :=
  factorConditionalKernel μ (invariantFactorMap G X) (measurable_invariantFactorMap G X)

instance invariantConditionalKernel_markov : IsMarkovKernel (invariantConditionalKernel (G := G) μ) := by
  unfold invariantConditionalKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

/-- Pull the conditional kernel back to the original space. -/
def invariantConditionalMeasures (x : X) : Measure X :=
  invariantConditionalKernel (G := G) μ (invariantFactorMap G X x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InverseCompactControl
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact regions in the inverse coupling

A compact family of evaluation points yields common compact averaging and
increment regions. Integrals on an inverse-chart strip are bounded by a
fixed Haar mass times the original section integral.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal Pointwise

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

/-- The first-coordinate projection of a compact strip in inverse
coordinates. Its Haar mass is the constant in the local error bound. -/
def inverseStripBase (B : Set G) : Set G :=
  Prod.fst '' (pairChartTransition.symm '' (univ ×ˢ B : Set (NormalizedPair G Λ × G)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InverseTransferIdentity
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual inverse-coefficient transfer

The inverse transfer is the negative inverse linear map applied to the
whole-fiber average. Its cocycle identity holds almost everywhere for each
fixed group element, exactly as required for an L² cocycle.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]

/-- The inverse-section transfer with its required inverse linear coefficient. -/
def inverseTheta (β : Measure G) (A : W ≃L[ℝ] W)
    (π l : G →* Multiplicative W) (φ : NormalizedPair G Λ → W)
    (p : NormalizedPair G Λ) : W := -A.symm (inverseAveragedTransfer β π l φ p)

/-- The actual inverse-height cocycle after adding the inverse transfer. -/
def inverseCocycleError (β : Measure G) (A : W ≃L[ℝ] W)
    (π l : G →* Multiplicative W) (φ : NormalizedPair G Λ → W)
    (y : G) (p : NormalizedPair G Λ) : W :=
  pairHeight π y p + inverseTheta β A π l φ (normalizedTranslate y p) -
    inverseTheta β A π l φ p - A.symm (π y).toAdd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LeftTangentTrivialization
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Left translation identifies the tangent fibers

The differential of translation back to the identity is an actual continuous
linear equivalence. Its matrix in any fixed local tangent chart varies
smoothly. These facts supply the frame for the left-invariant metric.
-/

noncomputable section
namespace PolycyclicRecognition

open Bundle Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]

theorem leftTranslate_leftLog (g : G) :
    (leftTranslateDerivative (E := E) g).comp (leftLogDerivative g) =
      ContinuousLinearMap.id ℝ E := by
  have he : (fun h : G => g * (g⁻¹ * h)) = id := by ext h; simp
  have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) g
    ((contMDiff_mul_left (a := g) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiff_mul_left (a := g⁻¹) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
  have hid : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * (g⁻¹ * h)) g :
      E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    let D : (G → G) → (E →L[ℝ] E) := fun f => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f g
    have hi : D id = ContinuousLinearMap.id ℝ E := mfderiv_id
    exact (congrArg D he).trans hi
  have hb : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) (g⁻¹ * g) :
      E →L[ℝ] E) = leftTranslateDerivative (E := E) g := by
    let D : G → (E →L[ℝ] E) := fun x => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) x
    exact congrArg D (inv_mul_cancel g)
  exact (congrArg (fun f : E →L[ℝ] E => f.comp (leftLogDerivative g)) hb).symm.trans
    (hd.symm.trans hid)

theorem leftLog_leftTranslate (g : G) :
    (leftLogDerivative (E := E) g).comp (leftTranslateDerivative g) =
      ContinuousLinearMap.id ℝ E := by
  have he : (fun h : G => g⁻¹ * (g * h)) = id := by ext h; simp
  have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) (1 : G)
    ((contMDiff_mul_left (a := g⁻¹) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiff_mul_left (a := g) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
  have hid : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * (g * h)) 1 :
      E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    let D : (G → G) → (E →L[ℝ] E) := fun f => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f 1
    have hi : D id = ContinuousLinearMap.id ℝ E := mfderiv_id
    exact (congrArg D he).trans hi
  have ha : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) (g * 1) :
      E →L[ℝ] E) = leftLogDerivative (E := E) g := by
    let D : G → (E →L[ℝ] E) := fun x => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) x
    exact congrArg D (mul_one g)
  exact (congrArg (fun f : E →L[ℝ] E => f.comp (leftTranslateDerivative g)) ha).symm.trans
    (hd.symm.trans hid)

def leftTangentEquiv (g : G) : E ≃L[ℝ] E where
  toFun := leftLogDerivative g
  invFun := leftTranslateDerivative g
  map_add' := (leftLogDerivative g).map_add
  map_smul' := (leftLogDerivative g).map_smul
  left_inv v := congrArg (fun f : E →L[ℝ] E => f v) (leftTranslate_leftLog g)
  right_inv v := congrArg (fun f : E →L[ℝ] E => f v) (leftLog_leftTranslate g)
  continuous_toFun := (leftLogDerivative g).continuous
  continuous_invFun := (leftTranslateDerivative g).continuous

theorem leftLogDerivative_mul (g h : G) :
    (leftLogDerivative (E := E) (g * h)).comp
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h) =
      leftLogDerivative (E := E) h := by
  have he : (fun k : G => (g * h)⁻¹ * (g * k)) = (fun k : G => h⁻¹ * k) := by
    funext k
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hc := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) h
    ((contMDiff_mul_left (a := (g * h)⁻¹) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiff_mul_left (a := g) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
  let D : (G → G) → (E →L[ℝ] E) := fun f => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f h
  exact hc.symm.trans (congrArg D he)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PullbackInnerProduct
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling an inner product back through a linear equivalence -/

noncomputable section
namespace PolycyclicRecognition

open Bornology Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem pullbackInner_pos (A : E ≃L[ℝ] F) (v : E) (hv : v ≠ 0) :
    0 < pullbackInner A.toContinuousLinearMap v v := by
  apply real_inner_self_pos.mpr
  exact fun h => hv (A.injective (h.trans (map_zero A).symm))

theorem pullbackInner_bounded (A : E ≃L[ℝ] F) :
    IsVonNBounded ℝ {v : E | pullbackInner A.toContinuousLinearMap v v < 1} := by
  apply ((NormedSpace.isVonNBounded_ball ℝ F 1).image A.symm.toContinuousLinearMap).subset
  intro v hv
  change pullbackInner A.toContinuousLinearMap v v < 1 at hv
  refine ⟨A v, ?_, A.symm_apply_apply v⟩
  rw [Metric.mem_ball, dist_zero_right]
  have h : ‖A v‖ ^ 2 < 1 := by
    simpa only [pullbackInner, ContinuousLinearMap.bilinearComp_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq, ContinuousLinearEquiv.coe_coe] using hv
  nlinarith [norm_nonneg (A v)]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LeftInvariantRiemannianMetric
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A left-invariant Riemannian metric

An inner product at the identity is transported by the actual differentials
of left translation. Its smoothness is checked in the tangent bundle charts.
-/

noncomputable section
namespace PolycyclicRecognition

open Bundle Bornology Set
open scoped Manifold ContDiff Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]

theorem leftInvariantInner_pos (e : E ≃L[ℝ] F) (g : G)
    (v : TangentSpace (𝓘(ℝ, E)) g) (hv : v ≠ 0) :
    0 < leftInvariantInner e g v v :=
  pullbackInner_pos (E := E) ((leftTangentEquiv (E := E) g).trans e) v hv

theorem leftInvariantInner_bounded (e : E ≃L[ℝ] F) (g : G) :
    IsVonNBounded ℝ {v : TangentSpace (𝓘(ℝ, E)) g | leftInvariantInner e g v v < 1} :=
  pullbackInner_bounded (E := E) ((leftTangentEquiv (E := E) g).trans e)

def leftInvariantRiemannianMetric (e : E ≃L[ℝ] F) :
    ContMDiffRiemannianMetric (𝓘(ℝ, E)) ∞ E (TangentSpace (𝓘(ℝ, E)) : G → Type _) where
  inner := leftInvariantInner e
  symm _g _v _w := real_inner_comm _ _
  pos := leftInvariantInner_pos e
  isVonNBounded := leftInvariantInner_bounded e
  contMDiff := contMDiff_leftInvariantInner e

theorem leftInvariantInner_mul (e : E ≃L[ℝ] F) (g h : G) (v w : E) :
    leftInvariantInner e (g * h)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h v)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h w) =
      leftInvariantInner e h v w := by
  have hv := congrArg (fun D : E →L[ℝ] E => D v) (leftLogDerivative_mul (E := E) g h)
  have hw := congrArg (fun D : E →L[ℝ] E => D w) (leftLogDerivative_mul (E := E) g h)
  change inner ℝ
    (e (leftLogDerivative (E := E) (g * h)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h v)))
    (e (leftLogDerivative (E := E) (g * h)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h w))) =
    inner ℝ (e (leftLogDerivative (E := E) h v)) (e (leftLogDerivative (E := E) h w))
  change leftLogDerivative (E := E) (g * h)
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h v) =
      leftLogDerivative (E := E) h v at hv
  change leftLogDerivative (E := E) (g * h)
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h w) =
      leftLogDerivative (E := E) h w at hw
  rw [hv, hw]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LeftInvariantRiemannianLength
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Left translation preserves the Riemannian length -/

noncomputable section
namespace PolycyclicRecognition

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology Bundle

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  (e : E ≃L[ℝ] F)

abbrev leftRiemannianBundle : RiemannianBundle (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
  ⟨(leftInvariantRiemannianMetric (G := G) e).toRiemannianMetric⟩

theorem leftRiemannian_inner (g : G) (v w : TangentSpace (𝓘(ℝ, E)) g) :
    letI := leftRiemannianBundle (G := G) e
    inner ℝ v w = leftInvariantInner e g v w := rfl

theorem norm_mfderiv_leftTranslation (g h : G) (v : TangentSpace (𝓘(ℝ, E)) h) :
    letI := leftRiemannianBundle (G := G) e
    ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h v‖ = ‖v‖ := by
  let := leftRiemannianBundle (G := G) e
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    leftRiemannian_inner, leftRiemannian_inner]
  exact leftInvariantInner_mul e g h v v

theorem pathELength_leftTranslation (g : G) {γ : ℝ → G} {a b : ℝ}
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 γ (Icc a b)) :
    letI := leftRiemannianBundle (G := G) e
    Manifold.pathELength (𝓘(ℝ, E)) (fun t => g * γ t) a b =
      Manifold.pathELength (𝓘(ℝ, E)) γ a b := by
  let := leftRiemannianBundle (G := G) e
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt := (hγ t ⟨ht.1.le, ht.2.le⟩).mdifferentiableWithinAt one_ne_zero
    |>.mdifferentiableAt (Icc_mem_nhds ht.1 ht.2)
  have hd := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) t
    ((contMDiff_mul_left (a := g) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp)) hγt
  have hv := congrArg (fun D => D (1 : TangentSpace (𝓘(ℝ, ℝ)) t)) hd
  change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t => g * γ t) t 1 =
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) (γ t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ t 1) at hv
  change ‖mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t => g * γ t) t 1‖ₑ =
    ‖mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ t 1‖ₑ
  calc
    _ = ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) (γ t)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ t 1)‖ₑ :=
      congrArg (fun v : TangentSpace (𝓘(ℝ, E)) (g * γ t) => ‖v‖ₑ) hv
    _ = _ := by simp only [enorm, nnnorm, norm_mfderiv_leftTranslation e]

theorem riemannianEDist_leftTranslation (g x y : G) :
    letI := leftRiemannianBundle (G := G) e
    Manifold.riemannianEDist (𝓘(ℝ, E)) (g * x) (g * y) =
      Manifold.riemannianEDist (𝓘(ℝ, E)) x y := by
  let := leftRiemannianBundle (G := G) e
  have hle (a u v : G) : Manifold.riemannianEDist (𝓘(ℝ, E)) (a * u) (a * v) ≤
      Manifold.riemannianEDist (𝓘(ℝ, E)) u v := by
    apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, h₀, h₁, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
    have hbound := Manifold.riemannianEDist_le_pathELength
      ((contMDiffOn_const (c := a)).mul hγ)
      (congrArg (a * ·) h₀) (congrArg (a * ·) h₁) (by norm_num : (0 : ℝ) ≤ 1)
    change Manifold.riemannianEDist (𝓘(ℝ, E)) (a * u) (a * v) ≤
      Manifold.pathELength (𝓘(ℝ, E)) (fun t => a * γ t) 0 1 at hbound
    rw [pathELength_leftTranslation e a hγ] at hbound
    exact hbound.trans_lt hlen
  apply le_antisymm (hle g x y)
  simpa only [inv_mul_cancel_left] using hle g⁻¹ (g * x) (g * y)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LeftInvariantRiemannianDistance
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compatible metric induced by the left-invariant Riemannian structure -/

noncomputable section
namespace PolycyclicRecognition

open Bundle
open scoped Manifold ContDiff Bundle

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] (e : E ≃L[ℝ] F)

abbrev leftRiemannianEMetric : EMetricSpace G := by
  letI := leftRiemannianBundle (G := G) e
  letI : IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
    ⟨⟨(leftInvariantRiemannianMetric (G := G) e).inner,
      (leftInvariantRiemannianMetric (G := G) e).contMDiff.continuous,
      fun _ _ _ => rfl⟩⟩
  exact EMetricSpace.ofRiemannianMetric (𝓘(ℝ, E)) G

abbrev leftRiemannianMetric [ConnectedSpace G] : MetricSpace G := by
  letI := leftRiemannianEMetric (G := G) e
  exact EMetricSpace.toMetricSpace edist_ne_top_of_connected

theorem leftRiemannianMetric_topology [ConnectedSpace G] :
    (leftRiemannianMetric (G := G) e).toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace G› := rfl

theorem leftRiemannianMetric_isometric [ConnectedSpace G] :
    letI := leftRiemannianMetric (G := G) e
    IsIsometricSMul G G := by
  let := leftRiemannianMetric (G := G) e
  refine ⟨fun g => ?_⟩
  intro x y
  exact riemannianEDist_leftTranslation e g x y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LinearConjugationCentralizer
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Commutation through invertible linear factors -/

namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem linear_commute_of_mul_equiv_right (T F : Module.End ℝ V) (e : V ≃ₗ[ℝ] V)
    (he : Commute T e.toLinearMap) (h : Commute T (F * e.toLinearMap)) : Commute T F := by
  have hc := h.mul_right (linear_commute_symm e T he)
  have hh : F * e.toLinearMap * e.symm.toLinearMap = F := by
    apply LinearMap.ext
    intro x
    change F (e (e.symm x)) = F x
    rw [e.apply_symm_apply]
  rwa [hh] at hc

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocalGeneratorOrbit
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjoint generators restricted to an open family of words

Only arbitrarily small prefixes are needed in the spanning proof. This lets
the conjugating words stay inside a specified open coordinate neighborhood.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Module
open scoped Topology

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def localBilinearOrbitSpan (B : V →L[ℝ] V →L[ℝ] V) (X : I → V)
    (good : List (I × ℝ) → Prop) : Submodule ℝ V :=
  Submodule.span ℝ {v | ∃ w, good w ∧ ∃ i, bilinearAdjointWord B X w (X i) = v}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RationalZeroCoefficientHomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rationally zero coefficients have rationally zero homology

The proof uses the actual tensor-coinvariant terms of the bar complex. It
requires no finite-generation assumption on the group or the coefficients.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G]

theorem rational_tensor_isZero (A B : Type) [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (hA : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] A))) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] (A ⊗[ℤ] B))) := by
  let : Subsingleton (ℚ ⊗[ℤ] A) := ModuleCat.subsingleton_of_isZero hA
  have hs : Subsingleton ((ℚ ⊗[ℤ] A) ⊗[ℤ] B) := by
    apply subsingleton_of_forall_eq 0
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
    | add x y hx hy => simp only [hx, hy, add_zero]
  let := hs
  let : Subsingleton (ℚ ⊗[ℤ] (A ⊗[ℤ] B)) :=
    (TensorProduct.assoc ℤ ℚ A B).symm.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalAbelianTorsion
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rationalization detects torsion in abelian groups -/
noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
variable {A : Type} [CommGroup A]

theorem rationalAbelianMap_eq_zero_iff_isOfFinOrder (a : A) :
    rationalAbelianMap (Additive.ofMul a) = 0 ↔ IsOfFinOrder a := by
  change (TensorProduct.mk ℤ ℚ (Additive A) 1) (Additive.ofMul a) = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)]
  constructor
  · rintro ⟨z, hz⟩
    apply isOfFinOrder_iff_zpow_eq_one.mpr
    refine ⟨(z : ℤ), mem_nonZeroDivisors_iff_ne_zero.mp z.property, ?_⟩
    exact congrArg Additive.toMul hz
  · intro ha
    obtain ⟨n, hn, hpow⟩ := ha.exists_pow_eq_one
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by omega)⟩, ?_⟩
    change (n : ℤ) • Additive.ofMul a = 0
    have he := congrArg Additive.ofMul hpow
    change n • Additive.ofMul a = 0 at he
    simpa only [natCast_zsmul] using he

theorem rationalAbelianSpace_isZero_iff_torsion :
    IsZero (ModuleCat.of ℚ (RationalAbelianSpace A)) ↔ ∀ a : A, IsOfFinOrder a := by
  constructor
  · intro h a
    let : Subsingleton (RationalAbelianSpace A) := ModuleCat.subsingleton_of_isZero h
    exact (rationalAbelianMap_eq_zero_iff_isOfFinOrder a).mp (Subsingleton.elim _ _)
  · intro h
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [hx, hy, add_zero]
    | tmul q a =>
      have ha := (rationalAbelianMap_eq_zero_iff_isOfFinOrder a.toMul).mpr (h a.toMul)
      change (1 : ℚ) ⊗ₜ[ℤ] a = 0 at ha
      have he := congrArg (fun x : RationalAbelianSpace A => q • x) ha
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_zero] using he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ChosenIntegralResolution
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A resolution with finitely generated covers whenever available

The initial free term is the regular module. Every subsequent term covers the
kernel of the preceding differential. The chosen presentation retains finite
generation whenever that kernel is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

abbrev integralFreeAugmentation : Rep.leftRegular ℤ G ⟶ trivialIntegral G :=
  Rep.leftRegularHom (trivialIntegral G) 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledFiniteChains
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite chains at a controlled scale

These submodules retain a finite set of allowed relative positions. They
provide the chain-level control needed for the remaining FP transfer argument.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {R G H : Type} [CommRing R] [Group G] [Group H] {n m : ℕ}

theorem controlledChainSpan_single {S : Set G} {x : Fin (n + 1) → G}
    (hx : IsControlledTuple S x) :
    MonoidAlgebra.single x 1 ∈ controlledChainSpan R G n S :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem controlledChainSpan_map {S : Set G} {T : Set H}
    (f : MonoidAlgebra R (Fin (n + 1) → G) →ₗ[R]
      MonoidAlgebra R (Fin (m + 1) → H))
    (hf : ∀ x, IsControlledTuple S x →
      f (MonoidAlgebra.single x 1) ∈ controlledChainSpan R H m T)
    {c : MonoidAlgebra R (Fin (n + 1) → G)} (hc : c ∈ controlledChainSpan R G n S) :
    f c ∈ controlledChainSpan R H m T := by
  have h : controlledChainSpan R G n S ≤ (controlledChainSpan R H m T).comap f := by
    apply Submodule.span_le.mpr
    rintro a ⟨x, hx, rfl⟩
    exact hf x hx
  exact h hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ControlledCochainHomotopy
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledGroupRingValue_apply _root_.OAI.PolycyclicRecognition.controlledGroupRingValue_one _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Close coarse maps give homotopic controlled pullbacks -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {G H R : Type} [Group G] [Group H] [CommRing R]

/-- The controlled-support estimate promotes the simplicial prism to an
actual homotopy between the two cochain maps. -/
def controlledCochainHomotopy (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite) :
    Homotopy (controlledCochainMap (R := R) e) (controlledCochainMap e') where
  hom := controlledPrismHom e e' hc
  zero i j h := by
    exact dite_eq_right h
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq _ (by simp : (ComplexShape.up ℕ).Rel 0 1),
        Homotopy.prevD_zero_cochainComplex, add_zero, controlledPrismHom_succ,
        controlledCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change controlledCochainPullback e 0 c =
        controlledPrism e e' hc (controlledCoboundary c) + controlledCochainPullback e' 0 c
      exact controlledPrism_equation_zero e e' hc c
    | succ n =>
      rw [dNext_eq _ (by simp : (ComplexShape.up ℕ).Rel (n + 1) (n + 2)),
        prevD_eq _ (by simp : (ComplexShape.up ℕ).Rel n (n + 1)),
        controlledPrismHom_succ, controlledPrismHom_succ,
        controlledCochainComplex_d, controlledCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change controlledCochainPullback e (n + 1) c =
        controlledPrism e e' hc (controlledCoboundary c) +
          controlledCoboundary (controlledPrism e e' hc c) +
            controlledCochainPullback e' (n + 1) c
      rw [add_comm (controlledPrism e e' hc (controlledCoboundary c))]
      exact controlledPrism_equation_succ e e' hc c

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HomogeneousRepresentationCochains
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledCoboundary_apply _root_.OAI.PolycyclicRecognition.controlledCochainComplex_d _root_.OAI.PolycyclicRecognition.controlledCochainMap_apply _root_.OAI.PolycyclicRecognition.controlledFace_apply _root_.OAI.PolycyclicRecognition.controlledLinearExtension_single _root_.OAI.PolycyclicRecognition.controlledPrismHom_succ _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled cochains as maps from the standard resolution

The coefficient at the identity of an equivariant group-ring-valued map
recovers the scalar cochain. Conversely diagonal translation reconstructs
that equivariant map, with finite support supplied by controlled-support estimates.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G R : Type} [Group G] [CommRing R] {n : ℕ}

def homogeneousGroupRingValue (c : controlledCochains R G n) (x : Fin (n + 1) → G) :
    MonoidAlgebra R G := (MonoidAlgebra.coeffLinearEquiv R).symm (controlledGroupRingValue c x)

@[simp] theorem homogeneousGroupRingValue_coeff (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (h : G) :
    (homogeneousGroupRingValue c x).coeff h = c (fun i => h⁻¹ * x i) := rfl

theorem homogeneousGroupRingValue_covariance (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (g : G) :
    homogeneousGroupRingValue c (g • x) =
      Representation.leftRegular R G g (homogeneousGroupRingValue c x) := by
  ext h
  simp only [homogeneousGroupRingValue_coeff, Representation.coeff_ofMulAction]
  exact controlledGroupRingValue_covariance c x g h

def homogeneousGroupRingLinear (c : controlledCochains R G n) :
    MonoidAlgebra R (Fin (n + 1) → G) →ₗ[R] MonoidAlgebra R G :=
  (Finsupp.linearCombination R (homogeneousGroupRingValue c)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem homogeneousGroupRingLinear_single (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (r : R) :
    homogeneousGroupRingLinear c (MonoidAlgebra.single x r) = r • homogeneousGroupRingValue c x := by
  simp [homogeneousGroupRingLinear]

/-- The reconstructed values give an actual morphism of group representations. -/
def homogeneousRepresentationCochain (c : controlledCochains R G n) :
    (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G :=
  Rep.ofHom
    { toLinearMap := homogeneousGroupRingLinear c
      isIntertwining' := fun g => by
        change (homogeneousGroupRingLinear c).comp (Representation.diagonal R G (n + 1) g) =
          (Representation.leftRegular R G g).comp (homogeneousGroupRingLinear c)
        refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
        change homogeneousGroupRingLinear c
            (Representation.diagonal R G (n + 1) g (MonoidAlgebra.single x 1)) =
          Representation.leftRegular R G g
            (homogeneousGroupRingLinear c (MonoidAlgebra.single x 1))
        simp only [Representation.ofMulAction_single,
          homogeneousGroupRingLinear_single, one_smul]
        exact homogeneousGroupRingValue_covariance c x g }

@[simp] theorem homogeneousRepresentationCochain_single_coeff
    (c : controlledCochains R G n) (x : Fin (n + 1) → G) :
    ((homogeneousRepresentationCochain c).hom (MonoidAlgebra.single x 1)).coeff 1 = c x := by
  change (homogeneousGroupRingLinear c (MonoidAlgebra.single x 1)).coeff 1 = c x
  simp

/-- Evaluation at the identity has controlled support for every equivariant
map from the homogeneous resolution. -/
theorem representationCochain_controlled
    (F : (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G) :
    (fun x => (F.hom (MonoidAlgebra.single x 1)).coeff 1) ∈
      controlledCochains R G n := by
  let f : (Fin n → G) → (G →₀ R) := fun a =>
    MonoidAlgebra.coeffLinearEquiv R (F.hom (MonoidAlgebra.single (Fin.cons 1 a) 1))
  have heq : (fun x => f (homogeneousCoordinates x).1 (homogeneousCoordinates x).2) =
      (fun x => (F.hom (MonoidAlgebra.single x 1)).coeff 1) := by
    funext x
    let z : Fin (n + 1) → G := Fin.cons 1 (fun i => (x 0)⁻¹ * x i.succ)
    have hz : x 0 • z = x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [z]
    have h := representationCochain_translate F z (x 0)
    rw [hz] at h
    exact h.symm
  rw [← heq]
  exact controlled_homogeneous_of_finsupp f

/-- Scalar coefficient extraction, with its support obligation proved. -/
def representationControlledCochain
    (F : (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G) :
    controlledCochains R G n :=
  ⟨fun x => (F.hom (MonoidAlgebra.single x 1)).coeff 1,
    representationCochain_controlled F⟩

@[simp] theorem representationControlledCochain_homogeneous
    (c : controlledCochains R G n) :
    representationControlledCochain (homogeneousRepresentationCochain c) = c := by
  apply Subtype.ext
  funext x
  exact homogeneousRepresentationCochain_single_coeff c x

@[simp] theorem homogeneousRepresentationCochain_controlled
    (F : (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G) :
    homogeneousRepresentationCochain (representationControlledCochain F) = F := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  change Fin (n + 1) → G at x
  change homogeneousGroupRingLinear (representationControlledCochain F)
      (MonoidAlgebra.single x 1) = F.hom (MonoidAlgebra.single x 1)
  rw [homogeneousGroupRingLinear_single, one_smul]
  ext h
  change (F.hom (MonoidAlgebra.single (fun i => h⁻¹ * x i) 1)).coeff 1 =
    (F.hom (MonoidAlgebra.single x 1)).coeff h
  have hx := representationCochain_translate (n := n) F (x : Fin (n + 1) → G) h⁻¹
  change (F.hom (MonoidAlgebra.single (fun i => h⁻¹ * x i) 1)).coeff 1 =
    (F.hom (MonoidAlgebra.single x 1)).coeff (h⁻¹)⁻¹ at hx
  simpa only [inv_inv] using hx

/-- Controlled scalar cochains are exactly the equivariant cochains with
coefficients in the left regular group ring. -/
def homogeneousRepresentationCochainEquiv :
    controlledCochains R G n ≃ₗ[R]
      ((Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G) where
  toFun := homogeneousRepresentationCochain
  invFun := representationControlledCochain
  left_inv := representationControlledCochain_homogeneous
  right_inv := homogeneousRepresentationCochain_controlled
  map_add' c d := by
    apply (Function.LeftInverse.injective homogeneousRepresentationCochain_controlled)
    apply Subtype.ext
    funext x
    change ((homogeneousRepresentationCochain (c + d)).hom
      (MonoidAlgebra.single x 1)).coeff 1 =
      ((homogeneousRepresentationCochain c).hom (MonoidAlgebra.single x 1) +
        (homogeneousRepresentationCochain d).hom (MonoidAlgebra.single x 1)).coeff 1
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (homogeneousRepresentationCochain_single_coeff (c + d) x).trans
      (congrArg₂ (· + ·) (homogeneousRepresentationCochain_single_coeff c x)
        (homogeneousRepresentationCochain_single_coeff d x)).symm
  map_smul' r c := by
    apply (Function.LeftInverse.injective homogeneousRepresentationCochain_controlled)
    apply Subtype.ext
    funext x
    change ((homogeneousRepresentationCochain (r • c)).hom
      (MonoidAlgebra.single x 1)).coeff 1 =
      (r • (homogeneousRepresentationCochain c).hom (MonoidAlgebra.single x 1)).coeff 1
    simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply]
    exact (homogeneousRepresentationCochain_single_coeff (r • c) x).trans
      (congrArg (r • ·) (homogeneousRepresentationCochain_single_coeff c x)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ControlledGroupCohomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.controlledCochainMap_apply _root_.OAI.PolycyclicRecognition.controlledLinearExtension_single _root_.OAI.PolycyclicRecognition.controlledPrismHom_succ _root_.OAI.PolycyclicRecognition.controlledPrismTerm_apply _root_.OAI.PolycyclicRecognition.controlledPrism_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled cochains compute group-ring cohomology

Coefficient extraction identifies the whole controlled complex with the
Hom complex of the standard projective resolution, including its differential.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G R : Type} [Group G] [CommRing R] {n : ℕ}

theorem homogeneousGroupRingLinear_coboundary (c : controlledCochains R G n) :
    homogeneousGroupRingLinear (controlledCoboundary c) =
      (homogeneousGroupRingLinear c).comp (Rep.standardComplex.d R G (n + 1)) := by
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply]
  ext h
  simp [homogeneousGroupRingLinear_single, homogeneousGroupRingValue_coeff,
    controlledCoboundary_apply, Function.comp_def]

theorem homogeneousRepresentationCochain_coboundary (c : controlledCochains R G n) :
    homogeneousRepresentationCochain (controlledCoboundary c) =
      (Rep.standardComplex R G).d (n + 1) n ≫ homogeneousRepresentationCochain c := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  change homogeneousGroupRingLinear (controlledCoboundary c) =
    (homogeneousGroupRingLinear c).comp ((Rep.standardComplex R G).d (n + 1) n).hom.toLinearMap
  rw [Rep.standardComplex.d_eq]
  exact homogeneousGroupRingLinear_coboundary c

/-- The controlled complex is the actual standard-resolution cochain complex. -/
def controlledStandardCochainIso :
    controlledCochainComplex R G ≅
      (Rep.standardComplex R G).linearYonedaObj R (Rep.leftRegular R G) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => homogeneousRepresentationCochainEquiv.toModuleIso) (by
      rintro i j (h : i + 1 = j)
      subst j
      rw [controlledCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change (Rep.standardComplex R G).d (i + 1) i ≫ homogeneousRepresentationCochain c =
        homogeneousRepresentationCochain (controlledCoboundary c)
      exact (homogeneousRepresentationCochain_coboundary c).symm)

/-- Controlled scalar homogeneous cohomology is group-ring cohomology. -/
def controlledGroupCohomologyIso (n : ℕ) :
    (controlledCochainComplex R G).homology n ≅
      groupCohomology (Rep.leftRegular R G) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) _ n).mapIso
    controlledStandardCochainIso ≪≫
      (groupCohomologyIso (Rep.leftRegular R G) n (Rep.standardResolution R G)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CoarseGroupRingCohomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse invariance of group-ring cohomology

The maps need not be homomorphisms. Their finite coarse errors provide the
controlled prism homotopies, and hence inverse maps on group-ring cohomology.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G H R : Type} [Group G] [Group H] [CommRing R]

@[simp] theorem controlledCochainMap_refl :
    controlledCochainMap (R := R) (GroupCoarseEquivalence.refl G) =
      𝟙 (controlledCochainComplex R G) := by
  ext n c
  rfl

/-- The coarse inverse produces inverse controlled cochain maps up to homotopy. -/
def controlledCochainHomotopyEquiv (e : GroupCoarseEquivalence G H) :
    HomotopyEquiv (controlledCochainComplex R G) (controlledCochainComplex R H) where
  hom := controlledCochainMap e.symm
  inv := controlledCochainMap e
  homotopyHomInvId := by
    have h := (controlledCochainHomotopy (R := R) (GroupCoarseEquivalence.refl G)
      (e.trans e.symm) e.left_error).symm
    simpa only [controlledCochainMap_refl, controlledCochainMap_trans] using h
  homotopyInvHomId := by
    have h := (controlledCochainHomotopy (R := R) (GroupCoarseEquivalence.refl H)
      (e.symm.trans e) e.right_error).symm
    simpa only [controlledCochainMap_refl, controlledCochainMap_trans] using h

/-- Coarse-equivalent groups have isomorphic controlled scalar cohomology. -/
def controlledCohomologyIso (e : GroupCoarseEquivalence G H) (n : ℕ) :
    (controlledCochainComplex R G).homology n ≅ (controlledCochainComplex R H).homology n where
  hom := HomologicalComplex.homologyMap (controlledCochainMap e.symm) n
  inv := HomologicalComplex.homologyMap (controlledCochainMap e) n
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact ((controlledCochainHomotopyEquiv (R := R) e).homotopyHomInvId.homologyMap_eq n).trans
      (HomologicalComplex.homologyMap_id _ _)
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact ((controlledCochainHomotopyEquiv (R := R) e).homotopyInvHomId.homologyMap_eq n).trans
      (HomologicalComplex.homologyMap_id _ _)

/-- The group-ring case of coarse cohomology invariance, with the actual
left regular representations and standard group cohomology. -/
def coarseGroupRingCohomologyIso (e : GroupCoarseEquivalence G H) (n : ℕ) :
    groupCohomology (Rep.leftRegular R G) n ≅ groupCohomology (Rep.leftRegular R H) n :=
  (controlledGroupCohomologyIso n).symm ≪≫ controlledCohomologyIso e n ≪≫
    controlledGroupCohomologyIso n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ControlledChainRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equivariant control of finite chains

Left translation preserves every relative-position bound. Consequently an
equivariant image of a finitely generated representation lies at one finite
scale in the homogeneous standard chains.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {R G : Type} [CommRing R] [Group G] {n : ℕ}

def controlledChainSubrepresentation (S : Set G) :
    Subrepresentation (Representation.ofMulAction R G (Fin (n + 1) → G)) where
  toSubmodule := controlledChainSpan R G n S
  apply_mem_toSubmodule g := by
    intro c hc
    apply controlledChainSpan_map (Representation.ofMulAction R G _ g) _ hc
    intro x hx
    rw [Representation.ofMulAction_single]
    exact controlledChainSpan_single (hx.left_translate g)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolyZExtension
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a torsion-free cyclic series by one cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G J : Type} [Group G] [Group J]

def cyclicSeriesSnoc {H K L : Subgroup G} {n : ℕ}
    (c : CyclicSeries H K n) (s : CyclicStep K L) : CyclicSeries H L (n + 1) where
  group i := if i ≤ n then c.group i else L
  first := by simpa using c.first
  last := by simp
  step i hi := by
    by_cases h : i < n
    · simpa only [ite_eq_left (show i ≤ n by omega), ite_eq_left (show i + 1 ≤ n by omega)]
        using c.step i h
    · have he : i = n := by omega
      subst i
      simpa only [ite_eq_left le_rfl, ite_eq_right (show ¬n + 1 ≤ n by omega), c.last] using s

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalNilpotentTorsion
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A nilpotent group with zero rational abelianization is torsion

The last lower-central layer is a quotient of a tensor product whose first
factor is the abelianization. The proof works for every nilpotency class and
does not require finite generation.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct IsMulCommutative commutatorElement
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem rational_abelianization_isZero_of_surjective {Q : Type} [Group Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (hG : IsZero (ModuleCat.of ℚ (RationalAbelianSpace (Abelianization G)))) :
    IsZero (ModuleCat.of ℚ (RationalAbelianSpace (Abelianization Q))) :=
  rational_module_isZero_of_surjective (Abelianization.map f).toAdditive.toIntLinearMap
    (abelianization_map_surjective f hf) hG

theorem lowerCentral_torsion_of_rational_abelianization_isZero (n : ℕ)
    (hbound : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (hG : IsZero (ModuleCat.of ℚ (RationalAbelianSpace (Abelianization G)))) :
    ∀ g : G, IsOfFinOrder g := by
  induction n generalizing G with
  | zero =>
    intro g
    have hg : g = 1 := by
      have hm : g ∈ (⊤ : Subgroup G) := Subgroup.mem_top g
      rw [show (⊤ : Subgroup G) = ⊥ from hbound] at hm
      exact hm
    rw [hg]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.zero_lt_one, one_pow 1⟩
  | succ n ih =>
    cases n with
    | zero =>
      let : IsMulCommutative G := (commutator_eq_bot_iff G).mp hbound
      let e : Additive (Abelianization G) ≃ₗ[ℤ] Additive G :=
        (Abelianization.equivOfComm (H := G)).symm.toAdditive.toIntLinearEquiv
      have hz := rational_module_isZero_of_surjective e.toLinearMap e.surjective hG
      exact rationalAbelianSpace_isZero_iff_torsion.mp hz
    | succ n =>
      let J := (⊤ : Subgroup G).lowerCentralSeries (n + 1)
      let N := (⊤ : Subgroup G).lowerCentralSeries n
      have hJcenter : J ≤ Subgroup.center G :=
        Subgroup.commutator_top_right_eq_bot_iff_le_center.mp hbound
      have hC : ⁅(⊤ : Subgroup G), N⁆ = J := Subgroup.commutator_comm _ _
      let q := QuotientGroup.mk' J
      have hq : Function.Surjective q := QuotientGroup.mk'_surjective J
      have hQbound : (⊤ : Subgroup (G ⧸ J)).lowerCentralSeries (n + 1) = ⊥ := by
        have hJmap : J.map q = ⊥ := by
          rw [Subgroup.map_eq_bot_iff]
          exact le_of_eq (QuotientGroup.ker_mk' J).symm
        have he := Subgroup.map_lowerCentralSeries (⊤ : Subgroup G) q (n + 1)
        rw [← MonoidHom.range_eq_map, q.range_eq_top_of_surjective hq] at he
        exact he.symm.trans hJmap
      have hQt := ih hQbound (rational_abelianization_isZero_of_surjective q hq hG)
      let f := q.comp N.subtype
      have hAc : f.range ≤ Subgroup.center (G ⧸ J) := by
        rintro _ ⟨b, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro a
        obtain ⟨g, rfl⟩ := hq a
        apply commutatorElement_eq_one_iff_mul_comm.mp
        change ⁅q g, q (b : G)⁆ = 1
        rw [← map_commutatorElement]
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [← hC]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) b.property
      let : IsMulCommutative f.range := ⟨⟨fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hAc a.property) b).symm⟩⟩
      let K := f.ker
      let e := QuotientGroup.quotientKerEquivRange f
      let : IsMulCommutative (N ⧸ K) := ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul, mul_comm])⟩⟩
      have hKc : K.map N.subtype ≤ Subgroup.center G := by
        rintro _ ⟨b, hb, rfl⟩
        apply hJcenter
        exact (QuotientGroup.eq_one_iff _).mp hb
      have hCc : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G := hC ▸ hJcenter
      let : IsMulCommutative J := ⟨⟨fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hJcenter a.property) b).symm⟩⟩
      let : IsMulCommutative (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) := hC.symm ▸ inferInstance
      have hT := rational_tensor_isZero (Additive (Abelianization G)) (Additive (N ⧸ K)) hG
      have hL := rational_module_isZero_of_surjective
        (centralLayerTensorSurjection N hCc K hKc)
        (centralLayerTensor_surjective N hCc K hKc) hT
      let e₁ : centralLayerSubmodule N ≃ₗ[ℤ] Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) :=
        (centralLayerAddEquiv N hCc).toIntLinearEquiv
      let e₂ : Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) ≃ₗ[ℤ] Additive J :=
        (MulEquiv.subgroupCongr hC).toAdditive.toIntLinearEquiv
      let eL := e₁.trans e₂
      have hJ := rational_module_isZero_of_surjective eL.toLinearMap eL.surjective hL
      have hJt : ∀ z : J, IsOfFinOrder z := rationalAbelianSpace_isZero_iff_torsion.mp hJ
      intro g
      obtain ⟨k, hk, hg⟩ := (hQt (q g)).exists_pow_eq_one
      have hgJ : g ^ k ∈ J := (QuotientGroup.eq_one_iff _).mp (by
        change q (g ^ k) = 1
        rw [map_pow]
        exact hg)
      obtain ⟨m, hm, hgm⟩ := (hJt ⟨g ^ k, hgJ⟩).exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
      rw [pow_mul]
      exact congrArg Subtype.val hgm

theorem nilpotent_torsion_of_rational_abelianization_isZero [Group.IsNilpotent G]
    (hG : IsZero (ModuleCat.of ℚ (RationalAbelianSpace (Abelianization G)))) :
    ∀ g : G, IsOfFinOrder g :=
  lowerCentral_torsion_of_rational_abelianization_isZero (Group.nilpotencyClass G)
    (Subgroup.lowerCentralSeries_nilpotencyClass (G := G)) hG

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalHomologyAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation on normal-subgroup homology with ambient coefficients -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2
variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal] (A : Rep k G)

theorem normalHomologyMap_mul (i : ℕ) (g h : G) :
    normalHomologyMap k N A i (g * h) =
      normalHomologyMap k N A i h ≫ normalHomologyMap k N A i g := by
  rw [normalHomologyMap, normalHomologyMap, normalHomologyMap, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · ext n
    exact congrArg (fun e : MulAut N => ((e n : N) : G)) (map_mul (MulAut.conjNormal (H := N)) g h)
  · apply LinearMap.ext
    intro x
    change A.ρ (g * h) x = A.ρ g (A.ρ h x)
    rw [map_mul, Module.End.mul_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeKernelTail
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the first coordinate of a free abelian quotient -/

noncomputable section
namespace PolycyclicRecognition

def latticeTail (n : ℕ) : IntegralLatticeGroup (n + 1) →* IntegralLatticeGroup n where
  toFun a := Multiplicative.ofAdd (fun i => a.toAdd i.succ)
  map_one' := rfl
  map_mul' _ _ := rfl

variable {G : Type} [Group G] {n : ℕ} (q : G →* IntegralLatticeGroup (n + 1))

def latticeKernelTail : ( (latticeCoordinate n).comp q).ker →* IntegralLatticeGroup n :=
  (latticeTail n).comp (q.comp ((latticeCoordinate n).comp q).ker.subtype)

def latticeKernelTailEquiv : q.ker ≃* (latticeKernelTail q).ker where
  toFun a := ⟨⟨a, by
    change latticeCoordinate n (q a) = 1
    rw [a.property, map_one]⟩, by
    change latticeTail n (q a) = 1
    rw [a.property, map_one]⟩
  invFun a := ⟨a.val.val, by
    apply Multiplicative.toAdd.injective
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg Multiplicative.toAdd a.val.property
    · exact congrFun (congrArg Multiplicative.toAdd a.property) j⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentTorsionSubgroup
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The characteristic torsion subgroup of a nilpotent group

Zero rational abelianization shows that a subgroup generated by torsion
elements is torsion. This constructs the subgroup and its torsion-free
quotient without a finite-generation premise.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_torsion_closure (S : Set G) (hS : ∀ g ∈ S, IsOfFinOrder g) :
    ∀ g ∈ Subgroup.closure S, IsOfFinOrder g := by
  let H := Subgroup.closure S
  let π := Abelianization.of (G := H)
  let T := (CommGroup.torsion (Abelianization H)).comap π
  have hHT : H ≤ T.map H.subtype := by
    change Subgroup.closure S ≤ T.map H.subtype
    rw [Subgroup.closure_le]
    intro g hg
    let a : H := ⟨g, Subgroup.subset_closure hg⟩
    refine ⟨a, ?_, rfl⟩
    change IsOfFinOrder (π a)
    obtain ⟨n, hn, he⟩ := (hS g hg).exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    rw [← map_pow]
    have ha : a ^ n = 1 := Subtype.ext he
    rw [ha, map_one]
  have hHAb : ∀ a : Abelianization H, IsOfFinOrder a := by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator H) a
    obtain ⟨b, hb, he⟩ := hHT g.property
    have hbg : b = g := Subtype.ext he
    exact hbg ▸ hb
  have ht : ∀ g : H, IsOfFinOrder g :=
    nilpotent_torsion_of_rational_abelianization_isZero
      (rationalAbelianSpace_isZero_iff_torsion.mpr hHAb)
  intro g hg
  obtain ⟨n, hn, he⟩ := (ht ⟨g, hg⟩).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Subtype.val he⟩

theorem nilpotent_torsion_mul {a b : G} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) :
    IsOfFinOrder (a * b) := by
  apply nilpotent_torsion_closure {a, b}
  · intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact ha
    · exact Set.mem_singleton_iff.mp hg ▸ hb
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

def nilpotentTorsionSubgroup : Subgroup G where
  carrier := {g | IsOfFinOrder g}
  one_mem' := isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.zero_lt_one, one_pow 1⟩
  mul_mem' := nilpotent_torsion_mul
  inv_mem' := IsOfFinOrder.inv

@[simp] theorem mem_nilpotentTorsionSubgroup (g : G) :
    g ∈ nilpotentTorsionSubgroup ↔ IsOfFinOrder g := Iff.rfl

instance nilpotentTorsionSubgroup_characteristic :
    (nilpotentTorsionSubgroup (G := G)).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e g hg
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨n, hn, he⟩ := ha.exists_pow_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  exact ⟨n, hn, by rw [← map_pow, he, map_one]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocallyNilpotentTorsion
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite torsion kernel of a locally nilpotent group with bounded torsion -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem locallyNilpotent_torsion_mul
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H)
    {a b : G} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) : IsOfFinOrder (a * b) := by
  let H : Subgroup G := Subgroup.closure {a, b}
  have hH : H.FG := (Subgroup.fg_iff H).mpr ⟨{a, b}, rfl, Set.toFinite _⟩
  let := hlocal H hH
  let aH : H := ⟨a, Subgroup.subset_closure (by simp)⟩
  let bH : H := ⟨b, Subgroup.subset_closure (by simp)⟩
  have haH : IsOfFinOrder aH := by
    obtain ⟨n, hn, he⟩ := ha.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext he⟩
  have hbH : IsOfFinOrder bH := by
    obtain ⟨n, hn, he⟩ := hb.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext he⟩
  obtain ⟨n, hn, he⟩ := (nilpotent_torsion_mul haH hbH).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Subtype.val he⟩

def locallyNilpotentTorsionSubgroup
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) : Subgroup G where
  carrier := {g | IsOfFinOrder g}
  one_mem' := isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.zero_lt_one, one_pow 1⟩
  mul_mem' := locallyNilpotent_torsion_mul hlocal
  inv_mem' := IsOfFinOrder.inv

variable (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H)

instance locallyNilpotentTorsionSubgroup_characteristic :
    (locallyNilpotentTorsionSubgroup hlocal).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e g hg
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨n, hn, he⟩ := ha.exists_pow_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  exact ⟨n, hn, by rw [← map_pow, he, map_one]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProperMetricMidpoints
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact midpoints by compact minimization -/

namespace PolycyclicRecognition

open Set Metric

theorem exists_midpoint_of_proper {X : Type*} [MetricSpace X] [ProperSpace X]
    (hmid : HasApproximateMidpoints X) (x y : X) :
    ∃ z : X, dist x z ≤ dist x y / 2 ∧ dist z y ≤ dist x y / 2 := by
  let f : X → ℝ := fun z => max (dist x z) (dist z y)
  have hnonempty : (closedBall x (dist x y + 1)).Nonempty :=
    ⟨x, by simp only [mem_closedBall, dist_self] <;> positivity⟩
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall x (dist x y + 1)).exists_isMinOn
    hnonempty (show ContinuousOn f _ from
      ((continuous_const.dist continuous_id).max
        (continuous_id.dist continuous_const)).continuousOn)
  have hbound : f z ≤ dist x y / 2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨w, h₁, h₂⟩ := hmid x y (min ε 1) (lt_min hε zero_lt_one)
    have hw : w ∈ closedBall x (dist x y + 1) := by
      rw [mem_closedBall, dist_comm w x]
      have := min_le_right ε (1 : ℝ)
      linarith [dist_nonneg (x := x) (y := y)]
    exact (hz hw).trans (max_le (h₁.trans (add_le_add_right (min_le_left ε 1) _))
      (h₂.trans (add_le_add_right (min_le_left ε 1) _)))
  exact ⟨z, (le_max_left _ _).trans hbound, (le_max_right _ _).trans hbound⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MidpointGrids
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic grids obtained by inserting metric midpoints -/

noncomputable section
namespace PolycyclicRecognition

variable {X : Type*} [MetricSpace X]

def metricMidpoint (h : HasMetricMidpoints X) (x y : X) : X :=
  Classical.choose (h x y)

theorem metricMidpoint_left (h : HasMetricMidpoints X) (x y : X) :
    dist x (metricMidpoint h x y) ≤ dist x y / 2 :=
  (Classical.choose_spec (h x y)).1

theorem metricMidpoint_right (h : HasMetricMidpoints X) (x y : X) :
    dist (metricMidpoint h x y) y ≤ dist x y / 2 :=
  (Classical.choose_spec (h x y)).2

def midpointGrid (h : HasMetricMidpoints X) (x y : X) : ℕ → ℕ → X
  | 0, k => if k = 0 then x else y
  | n + 1, k => if k % 2 = 0 then midpointGrid h x y n (k / 2)
      else metricMidpoint h (midpointGrid h x y n (k / 2))
        (midpointGrid h x y n (k / 2 + 1))

theorem midpointGrid_even (h : HasMetricMidpoints X) (x y : X) (n k : ℕ) :
    midpointGrid h x y (n + 1) (2 * k) = midpointGrid h x y n k := by
  simp [midpointGrid]

theorem midpointGrid_odd (h : HasMetricMidpoints X) (x y : X) (n k : ℕ) :
    midpointGrid h x y (n + 1) (2 * k + 1) =
      metricMidpoint h (midpointGrid h x y n k) (midpointGrid h x y n (k + 1)) := by
  simp [midpointGrid, Nat.add_div, Nat.add_mod]

theorem midpointGrid_zero (h : HasMetricMidpoints X) (x y : X) (n : ℕ) :
    midpointGrid h x y n 0 = x := by
  induction n with
  | zero => simp [midpointGrid]
  | succ n ih => exact (midpointGrid_even h x y n 0).trans ih

theorem midpointGrid_last (h : HasMetricMidpoints X) (x y : X) (n : ℕ) :
    midpointGrid h x y n (2 ^ n) = y := by
  induction n with
  | zero => simp [midpointGrid]
  | succ n ih => simpa only [pow_succ, Nat.mul_comm, midpointGrid_even] using ih

theorem midpointGrid_adjacent (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) {k : ℕ} (hk : k < 2 ^ n) :
    dist (midpointGrid h x y n k) (midpointGrid h x y n (k + 1)) ≤
      dist x y / (2 : ℝ) ^ n := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by simpa using hk
      simp [this, midpointGrid]
  | succ n ih =>
      have hkn : k / 2 < 2 ^ n := by
        rw [pow_succ] at hk
        omega
      have hbound := (div_le_div_of_nonneg_right (ih hkn) (by norm_num : (0 : ℝ) ≤ 2))
      have heq : dist x y / (2 : ℝ) ^ n / 2 = dist x y / (2 : ℝ) ^ (n + 1) := by
        rw [pow_succ, div_div]
      rw [heq] at hbound
      rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
      · have heqk : k = 2 * (k / 2) := by omega
        rw [heqk, midpointGrid_even, midpointGrid_odd]
        exact (metricMidpoint_left h _ _).trans hbound
      · have heqk : k = 2 * (k / 2) + 1 := by omega
        have heqnext : k + 1 = 2 * (k / 2 + 1) := by omega
        have hg := midpointGrid_odd h x y n (k / 2)
        rw [← heqk] at hg
        rw [hg, heqnext, midpointGrid_even]
        exact (metricMidpoint_right h _ _).trans hbound

theorem midpointGrid_dist (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ 2 ^ n) :
    dist (midpointGrid h x y n k) (midpointGrid h x y n l) ≤
      (l - k : ℕ) * (dist x y / (2 : ℝ) ^ n) := by
  induction l, hkl using Nat.le_induction with
  | base => simp
  | succ l hkl ih =>
      have hln : l < 2 ^ n := by omega
      have hdist := (dist_triangle (midpointGrid h x y n k)
        (midpointGrid h x y n l) (midpointGrid h x y n (l + 1))).trans
        (add_le_add (ih hln.le) (midpointGrid_adjacent h x y n hln))
      convert hdist using 1
      all_goals try with_reducible_and_instances rfl
      rw [show l + 1 - k = (l - k) + 1 by omega, Nat.cast_add, Nat.cast_one]
      ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IdealSectionBoxCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact linear coordinates for an ideal and its quotient

Pure quotient lifts have weight zero. In the adapted basis, projection
retains exactly those coordinates, and inclusion of the ideal retains
exactly the weighted ideal coordinates. This is the linear part of the
section-coordinate box comparison.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V I J : Type*} [LieRing V] [LieAlgebra ℝ V]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

include hlift in
theorem quotientLinearSection_rightInverse (q : V ⧸ U.toSubmodule) :
    U.toSubmodule.mkQ (quotientLinearSection U bQ lift q) = q := by
  have he : U.toSubmodule.mkQ.comp (quotientLinearSection U bQ lift) = LinearMap.id := by
    apply bQ.ext
    intro j
    simpa only [LinearMap.comp_apply, quotientLinearSection, Basis.constr_basis,
      LinearMap.id_apply] using hlift j
  exact congrArg (fun f : (V ⧸ U.toSubmodule) →ₗ[ℝ] (V ⧸ U.toSubmodule) => f q) he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentSectionRemainder
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the actual ideal section remainder

The remainder of an exponential after removing its pure quotient section
is computed with the finite BCH formula. Its ideal coordinates have a
polynomial bound in the original logarithm. No box comparison is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped BigOperators

variable {V I J : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

@[simp] theorem exponentialRescaleBasis_zero {K : Type*}
    (b : Basis K ℝ V) (s : K → ℝ) : exponentialRescaleBasis b s 0 = b := by
  apply Basis.eq_of_apply_eq
  intro j
  simp [exponentialRescaleBasis, Basis.unitsSMul_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentTorsionQuotientEndgame
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The finite-dimensional endgame modulo nilpotent torsion

Finite rational kernel rank gives a characteristic locally finite normal
subgroup whose removal leaves finite virtual integral cohomological dimension.
Neither the finiteness of this torsion subgroup nor the rank implication from
ambient FP-infinity is asserted here.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]

def normalNilpotentTorsionSubgroup : Subgroup G :=
  (nilpotentTorsionSubgroup (G := N)).map N.subtype

instance normalNilpotentTorsionSubgroup_normal : (normalNilpotentTorsionSubgroup N).Normal := by
  dsimp [normalNilpotentTorsionSubgroup]
  infer_instance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalEigencharacters
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Finite-index stabilizers of normal-subgroup eigenspaces

Conjugation permutes the common eigenvalue functions of a normal subgroup.
There are only finitely many nonzero common eigenspaces. Consequently every
one of them is invariant under a subgroup of finite index in the ambient
group. This separates the finite permutation from the linear action.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]
  (A : Subgroup G) [A.Normal]

def normalCommonEigenspace (ρ : G →* (V ≃ₗ[K] V)) (χ : A → K) : Submodule K V :=
  commonEigenspace (fun a : A => (ρ a).toLinearMap) χ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialTupleCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product volume under independent exponential coordinate charts -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal NNReal BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

def exponentialBasisHomeomorph {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (b : Basis (Fin n) ℝ L) :
    (Fin n → ℝ) ≃ₜ G :=
  (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart

def exponentialTupleCoordinates {n h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (b : Fin h → Basis (Fin n) ℝ L) : (Fin h → G) ≃ₜ (Fin h → Fin n → ℝ) :=
  Homeomorph.piCongrRight (fun i => (exponentialBasisHomeomorph e chart (b i)).symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedTupleDomain
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A correlated tuple set in a growing flat coordinate cube -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter Metric
open scoped Manifold Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

def flatExponentialTupleCoordinates {h m n : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (b : Fin h → Basis (Fin n) ℝ L)
    (flat : (Fin m → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ)) :
    (Fin h → G) ≃ₜ (Fin m → ℝ) :=
  (exponentialTupleCoordinates lie chart b).trans flat.symm.toHomeomorph

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialDerivationCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint polynomial coordinates of a nilpotent derivation flow -/

noncomputable section
namespace PolycyclicRecognition

variable {I L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

local instance polynomialDerivationCoordinatesRational : Module ℚ L :=
  Module.compHom L (algebraMap ℚ ℝ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalCentralLayers
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Rational actions on the upper central layers

Ambient conjugation preserves the characteristic upper central series.
On each central layer it therefore gives a rational linear action. Trivial
rational action implies trivial action on the layer itself, since the
successive quotients are torsion-free.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

def upperCentralLayerAut (i : ℕ) : G →* MulAut (CentralLayer F i) :=
  (MulAut.characteristic (Subgroup.center (F ⧸ Subgroup.upperCentralSeries F i))).comp
    ((characteristicQuotientAut (Subgroup.upperCentralSeries F i)).comp
      (MulAut.conjNormal (H := F)))

def rationalUpperCentralAction (i : ℕ) :
    G →* (RationalAbelianSpace (CentralLayer F i) ≃ₗ[ℚ]
      RationalAbelianSpace (CentralLayer F i)) :=
  rationalAbelianAut.comp (upperCentralLayerAut F i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalNilpotentQuotient
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A faithful rational action on the quotient by the nilpotent radical

The finitely many upper central layers give a direct-product vector space.
For a maximal nilpotent normal subgroup, the action kernel is exactly that
subgroup, by the proved central-filtration criterion.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

def centralLayersAction (c : ℕ) :
    G →* (CentralLayersSpace F c ≃ₗ[ℚ] CentralLayersSpace F c) where
  toFun g := LinearEquiv.piCongrRight (fun i : Fin c => rationalUpperCentralAction F i g)
  map_one' := by
    ext v i
    change rationalUpperCentralAction F i 1 (v i) = v i
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v i
    change rationalUpperCentralAction F i (g * h) (v i) =
      rationalUpperCentralAction F i g (rationalUpperCentralAction F i h (v i))
    rw [map_mul]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalRepresentationFunctor
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rationalization and restriction of scalars for group representations

The tensor extension is exact and left adjoint to scalar restriction. Thus it
preserves the projectives used in the finite rational-coefficient resolution.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

attribute [local instance] OAI.PolycyclicRecognition.instModuleRatVIntIntegralRestrictionRepresentation
def rationalRepresentationHomEquiv (A : Rep.{0} ℤ G) (B : Rep.{0} ℚ G) :
    (rationalizeRepresentation A ⟶ B) ≃ (A ⟶ integralRestrictionRepresentation B) where
  toFun f := Rep.ofHom ⟨(f.hom.toLinearMap.restrictScalars ℤ).comp
      (TensorProduct.mk ℤ ℚ A 1), fun g => by
    apply LinearMap.ext
    intro a
    exact Rep.hom_comm_apply f g ((1 : ℚ) ⊗ₜ[ℤ] a)⟩
  invFun f := Rep.ofHom ⟨rationalLinearExtension (show A →ₗ[ℤ] B from f.hom.toLinearMap), fun g => by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q a
    change q • (f.hom (A.ρ g a) : B) = B.ρ g (q • (f.hom a : B))
    erw [map_smul]
    exact congrArg (fun b : B => q • b) (Rep.hom_comm_apply f g a)⟩
  left_inv f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro q a
    change q • f.hom ((1 : ℚ) ⊗ₜ[ℤ] a) = f.hom (q ⊗ₜ[ℤ] a)
    have ht : q • ((1 : ℚ) ⊗ₜ[ℤ] a) = q ⊗ₜ[ℤ] a := by
      rw [TensorProduct.smul_tmul']
      change (q * 1) ⊗ₜ[ℤ] a = q ⊗ₜ[ℤ] a
      rw [mul_one]
    erw [← ht, map_smul]
  right_inv f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    change (1 : ℚ) • (f.hom a : B) = (f.hom a : B)
    exact one_smul _ _

def rationalRepresentationAdjunction :
    rationalizeRepresentationFunctor (G := G) ⊣ integralRestrictionFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := rationalRepresentationHomEquiv
    homEquiv_naturality_left_symm f g := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro q a
      rfl
    homEquiv_naturality_right := by intros; rfl }

instance instPreservesProjectiveObjectsRepIntRatRationalizeRepresentationFunctor : (rationalizeRepresentationFunctor (G := G)).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    rationalRepresentationAdjunction

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RepresentationDirectSum
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete sums of integral representations for the telescope resolution -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G : Type} [Group G] {ι : Type}

instance integralRepresentationSum_projective (A : ι → Rep.{0} ℤ G)
    [∀ i, Projective (A i)] : Projective (integralRepresentationSum A) where
  factors {E X} f e := by
    refine ⟨integralRepresentationSumDesc A E
      (fun i => Projective.factorThru (integralRepresentationSumInclusion A i ≫ f) e), ?_⟩
    apply integralRepresentationSum_hom_ext
    intro i
    rw [← Category.assoc, integralRepresentationSumInclusion_desc,
      Projective.factorThru_comp]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RepresentationSumExact
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_inclusion _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact direct sums of integral coefficient sequences -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G ι : Type} [Group G]

def integralRepresentationSumMap {A B : ι → Rep.{0} ℤ G} (f : ∀ i, A i ⟶ B i) :
    integralRepresentationSum A ⟶ integralRepresentationSum B := by
  classical
  exact Rep.ofHom ⟨DirectSum.lmap (fun i => (f i).hom.toLinearMap), fun g => by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change DirectSum.lmap (fun i => (f i).hom.toLinearMap)
        (DirectSum.lmap (fun i => (A i).ρ g) (DirectSum.lof ℤ ι _ i x)) =
      DirectSum.lmap (fun i => (B i).ρ g)
        (DirectSum.lmap (fun i => (f i).hom.toLinearMap) (DirectSum.lof ℤ ι _ i x))
    rw [DirectSum.lmap_lof, DirectSum.lmap_lof, DirectSum.lmap_lof, DirectSum.lmap_lof]
    exact congrArg (DirectSum.lof ℤ ι _ i) (Rep.hom_comm_apply (f i) g x)⟩

@[simp]
theorem integralRepresentationSumMap_apply {A B : ι → Rep.{0} ℤ G}
    (f : ∀ i, A i ⟶ B i) (x : integralRepresentationSum A) (i : ι) :
    ((integralRepresentationSumMap f).hom x) i = (f i).hom (x i) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RiemannianApproximateMidpoints
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Approximate midpoints for the Riemannian distance -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric Manifold
open scoped Manifold ContDiff Topology Bundle

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem leftRiemannianMetric_approximateMidpoints :
    letI := leftRiemannianMetric (G := G) e
    HasApproximateMidpoints G := by
  let metric := leftRiemannianMetric (G := G) e
  let bundle := leftRiemannianBundle (G := G) e
  intro x y ε hε
  have hr : riemannianEDist (𝓘(ℝ, E)) x y < ENNReal.ofReal (dist x y + ε) := by
    change edist x y < _
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]
    linarith
  obtain ⟨γ, h₀, h₁, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hcont : ContinuousOn (fun t => dist x (γ t)) (Icc (0 : ℝ) 1) :=
    continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)
  have hm : dist x y / 2 ∈ Icc (dist x (γ 0)) (dist x (γ 1)) := by
    rw [h₀, h₁, dist_self]
    constructor <;> linarith [dist_nonneg (x := x) (y := y)]
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc zero_le_one hcont hm
  have hleft : ENNReal.ofReal (dist x (γ t)) ≤ pathELength (𝓘(ℝ, E)) γ 0 t := by
    rw [← edist_dist]
    exact riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc le_rfl ht.2)) h₀ rfl ht.1
  have hright : ENNReal.ofReal (dist (γ t) y) ≤ pathELength (𝓘(ℝ, E)) γ t 1 := by
    rw [← edist_dist]
    exact riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc ht.1 le_rfl)) rfl h₁ ht.2
  have hsum : dist x (γ t) + dist (γ t) y < dist x y + ε := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (add_nonneg dist_nonneg dist_nonneg)).mp
    calc
      ENNReal.ofReal (dist x (γ t) + dist (γ t) y) =
          ENNReal.ofReal (dist x (γ t)) + ENNReal.ofReal (dist (γ t) y) :=
        ENNReal.ofReal_add dist_nonneg dist_nonneg
      _ ≤ pathELength (𝓘(ℝ, E)) γ 0 t + pathELength (𝓘(ℝ, E)) γ t 1 :=
        add_le_add hleft hright
      _ = pathELength (𝓘(ℝ, E)) γ 0 1 := pathELength_add ht.1 ht.2
      _ < _ := hlen
  refine ⟨γ t, ?_, ?_⟩ <;> linarith

theorem leftRiemannianMetric_proper [LocallyCompactSpace G] :
    letI := leftRiemannianMetric (G := G) e
    ProperSpace G := by
  let metric := leftRiemannianMetric (G := G) e
  let isometric := leftRiemannianMetric_isometric (G := G) e
  let groupTopology : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  exact properSpace_of_approximateMidpoints (leftRiemannianMetric_approximateMidpoints e)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequentialModuleTail
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the first stage of a sequential integral module colimit -/
noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2300] Module.DirectLimit.module
variable (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)]
  (f : ∀ i j, i ≤ j → M i →ₗ[ℤ] M j)
  [DirectedSystem M (fun i j h => f i j h)]

instance moduleTailMap_directed : DirectedSystem (fun i => M (i + 1))
    (fun i j h => moduleTailMap M f i j h) where
  map_self := by intro i x; exact Module.DirectedSystem.map_self (f := f) x
  map_map := by
    intro k j i hij hjk x
    exact Module.DirectedSystem.map_map (f := f)
      (Nat.add_le_add_right hij 1) (Nat.add_le_add_right hjk 1) x

def moduleTailToOriginal : ModuleTailLimit M f →ₗ[ℤ] Module.DirectLimit M f :=
  Module.DirectLimit.lift ℤ ℕ _ _
    (fun i => Module.DirectLimit.of ℤ ℕ M f (i + 1))
    (fun _ _ h x => Module.DirectLimit.of_f (R := ℤ) (f := f)
      (hij := Nat.add_le_add_right h 1) (x := x))

omit [DirectedSystem M (fun i j h => f i j h)] in
theorem moduleTailToOriginal_of (i : ℕ) (x : M (i + 1)) :
    moduleTailToOriginal M f (Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i x) =
      Module.DirectLimit.of ℤ ℕ M f (i + 1) x :=
  Module.DirectLimit.lift_of _ _ _

def moduleOriginalToTail : Module.DirectLimit M f →ₗ[ℤ] ModuleTailLimit M f :=
  Module.DirectLimit.lift ℤ ℕ _ _
    (fun i => (Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i).comp
      (f i (i + 1) (Nat.le_succ i))) (by
        intro i j h x
        change Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) j
          (f j (j + 1) (Nat.le_succ j) (f i j h x)) =
            Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i
              (f i (i + 1) (Nat.le_succ i) x)
        rw [Module.DirectedSystem.map_map]
        rw [← Module.DirectedSystem.map_map (f := f) (Nat.le_succ i)
          (Nat.add_le_add_right h 1) x]
        exact Module.DirectLimit.of_f (R := ℤ) (f := moduleTailMap M f)
          (hij := h) (x := f i (i + 1) (Nat.le_succ i) x))

@[simp]
theorem moduleOriginalToTail_of (i : ℕ) (x : M i) :
    moduleOriginalToTail M f (Module.DirectLimit.of ℤ ℕ M f i x) =
      Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i (f i (i + 1) (Nat.le_succ i) x) :=
  Module.DirectLimit.lift_of _ _ _

theorem moduleTail_original_inverse :
    (moduleTailToOriginal M f).comp (moduleOriginalToTail M f) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  change moduleTailToOriginal M f (moduleOriginalToTail M f
    (Module.DirectLimit.of ℤ ℕ M f i x)) = _
  rw [moduleOriginalToTail_of, moduleTailToOriginal_of]
  exact Module.DirectLimit.of_f (R := ℤ) (f := f) (hij := Nat.le_succ i) (x := x)

theorem moduleOriginal_tail_inverse :
    (moduleOriginalToTail M f).comp (moduleTailToOriginal M f) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  change moduleOriginalToTail M f (moduleTailToOriginal M f
    (Module.DirectLimit.of ℤ ℕ _ (moduleTailMap M f) i x)) = _
  rw [moduleTailToOriginal_of, moduleOriginalToTail_of]
  exact Module.DirectLimit.of_f (R := ℤ) (f := moduleTailMap M f)
    (hij := Nat.le_succ i) (x := x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnitaryQuotientCocycle
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending a central-trivial unitary cocycle to the central quotient -/

noncomputable section

namespace PolycyclicRecognition

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hz : ∀ z : Subgroup.center G, ρ z = 1)

variable {ρ hz} (b : G → E) (hb : IsUnitaryCocycle ρ b)
  (hbz : ∀ z : Subgroup.center G, b z = 0)

def centerQuotientCocycle : G ⧸ Subgroup.center G → E :=
  Quotient.lift b (fun a c hac => by
    have hm : a⁻¹ * c ∈ Subgroup.center G := QuotientGroup.leftRel_apply.mp hac
    have hzero := hbz ⟨a⁻¹ * c, hm⟩
    have he := hb a (a⁻¹ * c)
    simpa only [mul_inv_cancel_left, hzero, map_zero, add_zero] using he.symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UpperCentralLayerMap
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Equivariant rational maps from the actual upper central series -/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

omit [F.Normal] in
theorem mem_ambientUpperCentralSeries_iff (i : ℕ) (a : F) :
    (a : G) ∈ ambientUpperCentralSeries F i ↔ a ∈ Subgroup.upperCentralSeries F i := by
  constructor
  · rintro ⟨b, hb, he⟩
    have he' : b = a := Subtype.val_injective he
    cases he'
    exact hb
  · exact fun ha => ⟨a, ha, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactGeneratingBalls
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): the word API of `Group.Generators`
(`Mathlib/Geometry/Group/WordProd.lean` and `WordMetric.lean` there). -/

namespace OAI

/-! # Compact bounds for words in a compact symmetric generating set -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {G : Type*} [Group G] (K : Set G) (hK : Subgroup.closure K = ⊤)
  (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K)

include hsymm in
theorem generator_wordProd_mem_pow (l : List (K × Bool)) :
    (Group.Generators.ofSet hK).wordProd l ∈ K ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.length_cons, pow_succ', Group.Generators.wordProd_cons]
    apply Set.mul_mem_mul ?_ ih
    obtain ⟨k, b⟩ := b
    cases b with
    | false => exact (hsymm k).mpr k.property
    | true => exact k.property

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactSegmentLimit
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact limits of approximations to a minimizing segment -/

namespace PolycyclicRecognition

open Set Metric Filter
open scoped Topology

theorem exists_segment_of_compact_approximations {X : Type*} [MetricSpace X]
    [ProperSpace X] (x y : X)
    (f : ℕ → Icc (0 : ℝ) 1 → X) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (𝓝 0))
    (hzero : ∀ n, f n ⟨0, by simp⟩ = x)
    (hone : ∀ n, f n ⟨1, by simp⟩ = y)
    (hball : ∀ n t, dist (f n t) x ≤ dist x y)
    (hpair : ∀ n s t, dist (f n s) (f n t) ≤ dist x y * |(s : ℝ) - t| + err n) :
    ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) ≤ dist x y * |s - t| := by
  let K : Set (Icc (0 : ℝ) 1 → X) := univ.pi (fun _ => closedBall x (dist x y))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall x (dist x y)
  have hfK : ∀ᶠ n in atTop, f n ∈ K := Eventually.of_forall fun n t _ => hball n t
  obtain ⟨g, _, hg⟩ := hK.exists_mapClusterPt (le_principal_iff.mpr hfK)
  have gzero : g ⟨0, by simp⟩ = x :=
    (isClosed_eq (continuous_apply _) continuous_const).mem_of_mapClusterPt hg
      (Eventually.of_forall hzero)
  have gone : g ⟨1, by simp⟩ = y :=
    (isClosed_eq (continuous_apply _) continuous_const).mem_of_mapClusterPt hg
      (Eventually.of_forall hone)
  have gpair (s t : Icc (0 : ℝ) 1) :
      dist (g s) (g t) ≤ dist x y * |(s : ℝ) - t| := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have he := herr.eventually (gt_mem_nhds hε)
    have hclosed : IsClosed {v : Icc (0 : ℝ) 1 → X |
        dist (v s) (v t) ≤ dist x y * |(s : ℝ) - t| + ε} :=
      isClosed_le ((continuous_apply s).dist (continuous_apply t)) continuous_const
    apply hclosed.mem_of_mapClusterPt hg
    filter_upwards [he] with n hn
    exact (hpair n s t).trans (add_le_add_right hn.le _)
  classical
  let γ : ℝ → X := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then g ⟨t, ht⟩ else x
  refine ⟨γ, ?_, ?_, ?_⟩
  · simpa only [γ, dite_eq_left (show (0 : ℝ) ∈ Icc 0 1 by simp)] using gzero
  · simpa only [γ, dite_eq_left (show (1 : ℝ) ∈ Icc 0 1 by simp)] using gone
  · intro s hs t ht
    simpa only [γ, dite_eq_left hs, dite_eq_left ht] using gpair ⟨s, hs⟩ ⟨t, ht⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactWordCost
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted costs attached to a compact generating neighborhood

Inside the generating neighborhood use the original metric; outside it use
word length. This preserves the local topology while controlling word length.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]

variable (K : Set G) (hK : Subgroup.closure K = ⊤)

def compactWordLength (g : G) : ℕ := (compactWordGenerators K hK).wordLength g

omit [MetricSpace G] [IsIsometricSMul G G] in
theorem compactWordLength_le_one (g : G) (hg : g ∈ K) : compactWordLength K hK g ≤ 1 := by
  have h := (compactWordGenerators K hK).wordLength_wordProd_le [(⟨g, hg⟩, true)]
  simpa [compactWordLength, compactWordGenerators] using h

omit [MetricSpace G] [IsIsometricSMul G G] in
@[simp] theorem compactWordLength_one : compactWordLength K hK 1 = 0 := by
  simp [compactWordLength]

omit [MetricSpace G] [IsIsometricSMul G G] in
@[simp] theorem compactWordLength_inv (g : G) :
    compactWordLength K hK g⁻¹ = compactWordLength K hK g := by
  simp [compactWordLength]

def compactWordCost (g : G) : ℝ≥0 := by
  classical
  exact if g ∈ K then nndist 1 g else compactWordLength K hK g

omit [IsIsometricSMul G G] in
theorem compactWordCost_mem (g : G) (hg : g ∈ K) :
    compactWordCost K hK g = nndist 1 g := by simp [compactWordCost, hg]

variable (hbounded : ∀ x y : G, dist x y ≤ 1)

include hbounded in
omit [IsIsometricSMul G G] in
theorem metric_le_compactWordCost (g : G) : dist 1 g ≤ compactWordCost K hK g := by
  classical
  by_cases hg : g ∈ K
  · simp [compactWordCost, hg]
  · by_cases hgone : g = 1
    · simp [hgone, compactWordCost]
    · have hw : 1 ≤ compactWordLength K hK g := Nat.one_le_iff_ne_zero.mpr (by
        intro hz
        exact hgone ((compactWordGenerators K hK).wordLength_eq_zero_iff.mp hz))
      simpa [compactWordCost, hg] using
        (hbounded 1 g).trans (show (1 : ℝ) ≤ compactWordLength K hK g by exact_mod_cast hw)

theorem compactWordCost_inv (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K) (g : G) :
    compactWordCost K hK g⁻¹ = compactWordCost K hK g := by
  classical
  simp only [compactWordCost, hsymm, compactWordLength_inv]
  congr 1
  apply NNReal.eq
  exact (metricGroupNorm (G := G)).inv' g

def compactWeightedNorm (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K) : GroupNorm G :=
  weightedWordGroupNorm (compactWordCost K hK) (compactWordCost_inv K hK hsymm)
    metricGroupNorm (metric_le_compactWordCost K hK hbounded)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairChartSampling
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalized-pair identities for chart sampling

The action in this development is a left action obtained by inverting the
manuscript's right-translation parameter. The identities below keep that
inversion explicit.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

/-- Normalization at the actual chart point, including the deterministic
suffix between the two sampled factors. -/
def chartOccupationPoint (p : NormalizedPair G Λ) (x a k d : G) :
    NormalizedPair G Λ := normalizedTranslate (x * a * k * d) p

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoordinateChartSampling
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coordinate maps of the actual two-factor chart samples -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped NNReal

variable {G N D LN LD : Type*} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [Group N] [Group D]
  [LieRing LN] [LieAlgebra ℝ LN] [LieRing LD] [LieAlgebra ℝ LD]
  {n d : ℕ} {Λ : ℝ≥0}

/-- The chart sample uses the actual factor exponentials and includes the
deterministic enlarged suffix. -/
def coordinateChartPoint (p : NormalizedPair G Λ) (x : G)
    (ι : N →* G) (κ : D →* G) (ExpN : LN → N) (ExpD : LD → D)
    (bN : Basis (Fin n) ℝ LN) (bD : Basis (Fin d) ℝ LD) (k : N)
    (z : (Fin n → ℝ) × (Fin d → ℝ)) : NormalizedPair G Λ :=
  chartOccupationPoint p x (ι (ExpN (bN.equivFun.symm z.1)))
    (ι k) (κ (ExpD (bD.equivFun.symm z.2)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InvariantMeanGenerators
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # It suffices to make a mean invariant under a generating set -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology

variable {G : Type*} [Group G]

/-- The left translations preserving a linear averaging functional form a subgroup. -/
def meanStabilizer (M : BoundedReal G →ₗ[ℝ] ℝ) : Subgroup G where
  carrier := {g | ∀ f, M (leftPull g f) = M f}
  one_mem' := by intro f; rw [leftPull_one]
  mul_mem' := by
    intro g h hg hh f
    rw [leftPull_mul, hh, hg]
  inv_mem' := by
    intro g hg f
    have h := hg (leftPull g⁻¹ f)
    simpa only [← leftPull_mul, inv_mul_cancel, leftPull_one] using h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Thompson_FiniteAverage
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real finite averages and left-translation cancellation

These are literal finite sums. The translation estimate cancels the common
intersection of the two finite sets, and the function bound is global. No
invariant mean, support assumption, or limiting average is used.
-/

noncomputable section

universe uα uι uG

namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {α : Type uα} {ι : Type uι}

theorem realAvg_mono (A : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ A, f x ≤ g x) : realAvg A f ≤ realAvg A g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfg)
    (inv_nonneg.mpr (Nat.cast_nonneg A.card))

theorem realAvg_nonneg (A : Finset α) {f : α → ℝ}
    (hf : ∀ x ∈ A, 0 ≤ f x) : 0 ≤ realAvg A f := by
  simpa only [realAvg_zero] using realAvg_mono A hf

theorem realAvg_const (A : Finset α) (hA : A.Nonempty) (c : ℝ) :
    realAvg A (fun _ => c) = c := by
  have hc : (A.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hA))
  simp [realAvg, nsmul_eq_mul, hc]

end ThompsonNonamenability

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CyclicInvariantMean
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariant means on cyclic groups from literal power averages -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology BigOperators ENNReal

variable {G : Type*} [Group G]

def cyclicMeanState (a : G) (n : ℕ) : BoundedReal G →ₗ[ℝ] ℝ where
  toFun f := realAvg (Finset.range (n + 1)) (fun k => f (a ^ k))
  map_add' _f _g := realAvg_add _ _ _
  map_smul' r _f := realAvg_const_mul _ r _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteKernelCoarseEquivalence
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite kernels do not change the discrete group coarse structure -/
noncomputable section
namespace PolycyclicRecognition
variable {G Q : Type*} [Group G] [Group Q]

def finiteKernelCoarseEquivalence (q : G →* Q) (hq : Function.Surjective q)
    [Finite q.ker] : GroupCoarseEquivalence G Q := by
  let s := Function.surjInv hq
  have hs : ∀ x, q (s x) = x := Function.surjInv_eq hq
  refine ⟨q, s, groupBornologous_hom q, ?_, ?_, ?_⟩
  · intro S hS
    refine ⟨q ⁻¹' S, finite_kernel_preimage_finite q S hS, ?_⟩
    intro x y hxy
    change q ((s x)⁻¹ * s y) ∈ S
    simpa only [map_mul, map_inv, hs] using hxy
  · apply (Set.toFinite (q.ker : Set G)).subset
    rintro _ ⟨g, rfl⟩
    change q (g⁻¹ * s (q g)) = 1
    rw [map_mul, map_inv, hs, inv_mul_cancel]
  · apply (Set.finite_singleton (1 : Q)).subset
    rintro _ ⟨y, rfl⟩
    simp only [Set.mem_singleton_iff, hs, inv_mul_cancel]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteSupportInterpolation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible interpolation on finite supports -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {I G : Type*} [LinearOrder I] [MetricSpace G]

def finiteSupportCenter (c : ControlledContraction G) (p₀ : G) (v : I → G) (a : I →₀ ℝ) : G :=
  orderedCenter c p₀ v a (a.support.sort (· ≤ ·))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FolnerInvariantMean
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Følner averages yield the invariant mean for height correction -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter
open scoped Topology ENNReal

variable {G : Type*} [Group G] [DecidableEq G]

/-- A literal uniform average over a finite set, as a linear functional on
the actual space of bounded real functions. -/
def finiteMeanState (A : Finset G) : BoundedReal G →ₗ[ℝ] ℝ where
  toFun f := realAvg A f
  map_add' f g := realAvg_add A f g
  map_smul' r f := realAvg_const_mul A r f

omit [Group G] [DecidableEq G] in
theorem finiteMeanState_positive (A : Finset G) (f : BoundedReal G)
    (hf : ∀ g, 0 ≤ f g) : 0 ≤ finiteMeanState A f :=
  realAvg_nonneg A (fun g _ => hf g)

omit [Group G] [DecidableEq G] in
theorem finiteMeanState_one (A : Finset G) (hA : A.Nonempty) :
    finiteMeanState A 1 = 1 := realAvg_const A hA 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HorseshoeCover
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A projective cover adapted to a short exact coefficient sequence

The middle cover is the product of the two endpoint free covers. Its kernel
will provide an exact sequence of syzygies, without claiming that the
normalized free-cover functor itself is exact.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem rep_kernel_element {A B : Rep.{0} ℤ G} (f : A ⟶ B) (x : A)
    (hx : f.hom x = 0) : ∃ y : (kernel f : Rep.{0} ℤ G), (kernel.ι f).hom y = x :=
  (rep_shortComplex_exact_iff (ShortComplex.mk (kernel.ι f) f (kernel.condition f))).mp
    (ShortComplex.exact_kernel f) x hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralQuotientKernel
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing one coordinate from an integral abelian quotient -/

noncomputable section
namespace PolycyclicRecognition

theorem integralQuotient_eq_one {n : ℕ} (z : IntegralLatticeGroup (n + 1))
    (hd : integralQuotientDrop n z = 1) (hl : integralQuotientLast n z = 1) : z = 1 := by
  apply Multiplicative.ext
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · exact congrArg Multiplicative.toAdd hl
  · exact congrFun (congrArg Multiplicative.toAdd hd) k

variable {N G : Type} [Group N] [Group G] {n : ℕ}

def integralLastMap (E : GroupExtension N G (IntegralLatticeGroup (n + 1))) :
    G →* Multiplicative ℤ := (integralQuotientLast n).comp E.rightHom

def integralKernelInl (E : GroupExtension N G (IntegralLatticeGroup (n + 1))) :
    N →* (integralLastMap E).ker := E.inl.codRestrict _ (by
  intro x
  change integralQuotientLast n (E.rightHom (E.inl x)) = 1
  rw [E.rightHom_inl, map_one])

def integralKernelRight (E : GroupExtension N G (IntegralLatticeGroup (n + 1))) :
    (integralLastMap E).ker →* IntegralLatticeGroup n :=
  (integralQuotientDrop n).comp (E.rightHom.comp (integralLastMap E).ker.subtype)

def integralKernelExtension (E : GroupExtension N G (IntegralLatticeGroup (n + 1))) :
    GroupExtension N (integralLastMap E).ker (IntegralLatticeGroup n) where
  inl := integralKernelInl E
  rightHom := integralKernelRight E
  inl_injective := by
    intro x y h
    exact E.inl_injective (congrArg Subtype.val h)
  range_inl_eq_ker_rightHom := by
    ext h
    constructor
    · rintro ⟨x, rfl⟩
      change integralQuotientDrop n (E.rightHom (E.inl x)) = 1
      rw [E.rightHom_inl, map_one]
    · intro hh
      have he : E.rightHom h = 1 := integralQuotient_eq_one _ hh h.property
      have hr : (h : G) ∈ E.inl.range := by
        rw [E.range_inl_eq_ker_rightHom]
        exact he
      obtain ⟨x, hx⟩ := hr
      exact ⟨x, Subtype.ext hx⟩
  rightHom_surjective := by
    intro z
    obtain ⟨g, hg⟩ := E.rightHom_surjective (integralQuotientInsert n z 1)
    have hk : g ∈ (integralLastMap E).ker := by
      change integralQuotientLast n (E.rightHom g) = 1
      rw [hg, integralQuotientLast_insert]
    refine ⟨⟨g, hk⟩, ?_⟩
    change integralQuotientDrop n (E.rightHom g) = z
    rw [hg, integralQuotientDrop_insert]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearSupportSymmetries
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebraic support symmetries

The finite symmetry conclusion does not require a preselected norm or
topology on the finite-dimensional height quotient.
-/

noncomputable section

namespace PolycyclicRecognition

variable {W I B : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [Fintype B] [Nonempty B]

/-- The algebraic finite group of possible segment-support symmetries. -/
def linearSupportSymmetryGroup (D : SupportDatum W I B) : Subgroup (W ≃ₗ[ℝ] W) where
  carrier := {A | ∀ w, D.segmentSupport (A w) = D.segmentSupport w}
  one_mem' := fun _ => rfl
  mul_mem' := fun hA hB w => (hA _).trans (hB w)
  inv_mem' := by
    intro A hA w
    change D.segmentSupport (A.symm w) = D.segmentSupport w
    simpa only [LinearEquiv.apply_symm_apply] using (hA (A.symm w)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MidpointStepPaths
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Step paths through successively refined midpoint grids -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {X : Type*} [MetricSpace X]

def midpointStepPath (h : HasMetricMidpoints X) (x y : X) (n : ℕ)
    (t : Icc (0 : ℝ) 1) : X :=
  midpointGrid h x y n ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊

theorem midpointStepPath_zero (h : HasMetricMidpoints X) (x y : X) (n : ℕ) :
    midpointStepPath h x y n ⟨0, by simp⟩ = x := by
  simp [midpointStepPath, midpointGrid_zero]

theorem midpointStepPath_one (h : HasMetricMidpoints X) (x y : X) (n : ℕ) :
    midpointStepPath h x y n ⟨1, by simp⟩ = y := by
  have heq : ⌊(2 : ℝ) ^ n⌋₊ = 2 ^ n := by
    rw [← Nat.cast_ofNat, ← Nat.cast_pow, Nat.floor_natCast]
  simp only [midpointStepPath, mul_one, heq, midpointGrid_last]

theorem midpointStepPath_ball (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) (t : Icc (0 : ℝ) 1) :
    dist (midpointStepPath h x y n t) x ≤ dist x y := by
  have hk : ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊ ≤ 2 ^ n := by
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_of_le_one_right (by positivity) t.property.2
  have hb := midpointGrid_dist h x y n (Nat.zero_le _) hk
  rw [midpointGrid_zero, Nat.sub_zero] at hb
  rw [dist_comm]
  apply hb.trans
  have hk' : (⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊ : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hk
  calc
    _ ≤ (2 : ℝ) ^ n * (dist x y / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right hk' (by positivity)
    _ = dist x y := by field_simp

theorem midpointStepPath_dist_of_le (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) (s t : Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t) :
    dist (midpointStepPath h x y n s) (midpointStepPath h x y n t) ≤
      dist x y * ((t : ℝ) - s) + dist x y / (2 : ℝ) ^ n := by
  let k := ⌊(2 : ℝ) ^ n * (s : ℝ)⌋₊
  let l := ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊
  have hkl : k ≤ l := Nat.floor_mono (mul_le_mul_of_nonneg_left hst (by positivity))
  have hl : l ≤ 2 ^ n := by
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_of_le_one_right (by positivity) t.property.2
  have hb := midpointGrid_dist h x y n hkl hl
  change dist (midpointStepPath h x y n s) (midpointStepPath h x y n t) ≤ _ at hb
  apply hb.trans
  rw [Nat.cast_sub hkl]
  have hs := Nat.lt_floor_add_one ((2 : ℝ) ^ n * (s : ℝ))
  have ht := Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n) t.property.1)
  change (2 : ℝ) ^ n * (s : ℝ) < (k : ℝ) + 1 at hs
  change (l : ℝ) ≤ (2 : ℝ) ^ n * (t : ℝ) at ht
  have hdiff : (l : ℝ) - k ≤ (2 : ℝ) ^ n * ((t : ℝ) - s) + 1 := by nlinarith
  calc
    _ ≤ ((2 : ℝ) ^ n * ((t : ℝ) - s) + 1) * (dist x y / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ = _ := by field_simp

theorem midpointStepPath_dist (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) (s t : Icc (0 : ℝ) 1) :
    dist (midpointStepPath h x y n s) (midpointStepPath h x y n t) ≤
      dist x y * |(s : ℝ) - t| + dist x y / (2 : ℝ) ^ n := by
  rcases le_total (s : ℝ) t with hst | hts
  · rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    convert midpointStepPath_dist_of_le h x y n s t hst using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
    exact midpointStepPath_dist_of_le h x y n t s hts

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MetricSegmentsFromMidpoints
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Minimizing segments from properness and approximate midpoints -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology

theorem exists_metric_segment {X : Type*} [MetricSpace X] [ProperSpace X]
    (hmid : HasApproximateMidpoints X) (x y : X) :
    ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) ≤ dist x y * |s - t| := by
  let h : HasMetricMidpoints X := exists_midpoint_of_proper hmid
  apply exists_segment_of_compact_approximations x y (midpointStepPath h x y)
    (fun n => dist x y / (2 : ℝ) ^ n)
  · exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_div_atTop _
  · exact midpointStepPath_zero h x y
  · exact midpointStepPath_one h x y
  · exact midpointStepPath_ball h x y
  · exact midpointStepPath_dist h x y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledBasisScaleChange
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing the physical scale of one exponential basis -/

namespace PolycyclicRecognition

open Module

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem repr_scale_exponentialRescaleBasis (b : Basis J ℝ L)
    (c : J → ℝ) (r t : ℝ) (x : L) (j : J) :
    (exponentialRescaleBasis b c r).repr x j =
      (exponentialRescaleBasis b c t).repr x j * Real.exp ((t - r) * c j) := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, ← Real.exp_neg]
  have he : Real.exp (-(t * c j)) * Real.exp ((t - r) * c j) =
      Real.exp (-(r * c j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_right_comm, he]

/-- The exact change in scale is bounded by the largest change in a
coordinate exponent. There is no asymptotic hypothesis in this estimate. -/
theorem norm_scale_exponentialRescaleBasis_le [Fintype J]
    (b : Basis J ℝ L) (c : J → ℝ) (r t A : ℝ)
    (hgap : ∀ j, (t - r) * c j ≤ A) (x : L) :
    ‖(exponentialRescaleBasis b c r).equivFun x‖ ≤
      Real.exp A * ‖(exponentialRescaleBasis b c t).equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro j
  change |(exponentialRescaleBasis b c r).repr x j| ≤ _
  rw [repr_scale_exponentialRescaleBasis, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ‖(exponentialRescaleBasis b c t).equivFun x‖ * Real.exp A :=
      mul_le_mul (norm_le_pi_norm ((exponentialRescaleBasis b c t).equivFun x) j)
        (Real.exp_le_exp.mpr (hgap j)) (Real.exp_pos _).le (norm_nonneg _)
    _ = _ := mul_comm _ _

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RightFolnerExpansion
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right finite expansions and metric Følner sets in the source group

Left-invariant metrics use right expansions of finite sets. Inversion
converts the left Følner sets supplied by an invariant mean into these sets.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped symmDiff

variable {G : Type*} [Group G] [DecidableEq G]

variable [MetricSpace G] [IsIsometricSMul G G]

/-- A source metric neighborhood is a right expansion by the finite identity
ball. This is the exact finite set used in the boundary estimate. -/
def finiteMetricNeighborhood (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    (E : Finset G) (R : ℝ) : Finset G :=
  rightFiniteExpansion E ((hfinite R).toFinset)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SmallCoefficientRing
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small ring of bounded functions with finite-subgroup projectivity

For each finite subgroup choose its right-coset transversal. Take the Boolean
algebra generated by every left translate of these transversals and of
subgroup coset partitions inside finitely generated subgroups. When the group
is countable, this uses countably many coordinates. Its step-function ring is
projective over the integers and has a trace-one element for every finite
subgroup.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance] Classical.propDecidable
variable (G : Type) [Group G]

set_option synthInstance.maxHeartbeats 400000 in
instance finiteSubgroupIndex_countable [Countable G] : Countable (finiteSubgroupIndex G) := by
  apply Function.Injective.countable (f := finiteSubgroupElements G)
  intro H K h
  apply Subtype.ext
  apply SetLike.coe_injective
  simpa only [finiteSubgroupElements_coe] using congrArg (fun s : Finset G => (s : Set G)) h

set_option synthInstance.maxHeartbeats 400000 in
instance finiteSubgroupIndex_nonempty : Nonempty (finiteSubgroupIndex G) :=
  ⟨⟨⊥, inferInstance⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
def finitelyGeneratedSubgroupGenerators (H : finitelyGeneratedSubgroupIndex G) : Finset G :=
  Classical.choose H.property

set_option synthInstance.maxHeartbeats 400000 in
instance finitelyGeneratedSubgroupIndex_countable [Countable G] :
    Countable (finitelyGeneratedSubgroupIndex G) := by
  apply Function.Injective.countable (f := finitelyGeneratedSubgroupGenerators G)
  intro H K h
  apply Subtype.ext
  have hH := Classical.choose_spec H.property
  have hK := Classical.choose_spec K.property
  change Subgroup.closure (finitelyGeneratedSubgroupGenerators G H : Set G) = H.val at hH
  change Subgroup.closure (finitelyGeneratedSubgroupGenerators G K : Set G) = K.val at hK
  rw [← hH, ← hK, h]

set_option synthInstance.maxHeartbeats 400000 in
/-- The coefficient ring with its actual translation representation. -/
abbrev smallCoefficientRepresentation : Rep ℤ G :=
  ringActionRepresentation (H := G) (R := SmallCoefficientRing G)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SmallCoefficientMean
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An invariant mean on the actual bounded coefficient ring

Every ring element has finite range. Evaluation as a real bounded function is
therefore defined without any extra boundedness premise.
-/
noncomputable section
namespace PolycyclicRecognition
open ThompsonNonamenability
open scoped ENNReal
variable {G : Type} [Group G]

theorem smallCoefficientBoundedReal_translate (g : G) (f : SmallCoefficientRing G) :
    smallCoefficientBoundedReal (g • f) = leftPull g⁻¹ (smallCoefficientBoundedReal f) := by
  apply lp.ext
  funext x
  rfl

theorem smallCoefficientRealMean_invariant (M : InvariantMean G)
    (g : G) (f : SmallCoefficientRing G) :
    smallCoefficientRealMean M (g • f) = smallCoefficientRealMean M f := by
  change M.toLinearMap (smallCoefficientBoundedReal (g • f)) = _
  rw [smallCoefficientBoundedReal_translate, M.left_invariant]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SmallCoefficientRationalMean
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An invariant rational functional on the rationalized coefficient ring

The real mean proves that the constant class is nonzero in coinvariants.
Linear separation over the rationals then supplies a rational functional;
no rational-valued positive mean on all bounded functions is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open ThompsonNonamenability Representation
open scoped TensorProduct
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientRationalAction : Representation ℚ G (SmallCoefficientRationalSpace (G := G)) where
  toFun g := ((smallCoefficientRepresentation G).ρ g).baseChange ℚ
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q b
    change q ⊗ₜ[ℤ] ((smallCoefficientRepresentation G).ρ 1 b) = q ⊗ₜ[ℤ] b
    rw [map_one]
    rfl
  map_mul' g h := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q b
    change q ⊗ₜ[ℤ] ((smallCoefficientRepresentation G).ρ (g * h) b) =
      q ⊗ₜ[ℤ] ((smallCoefficientRepresentation G).ρ g ((smallCoefficientRepresentation G).ρ h b))
    rw [map_mul]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientRationalRealMean (M : InvariantMean G) :
    SmallCoefficientRationalSpace (G := G) →ₗ[ℚ] ℝ :=
  rationalLinearExtension (smallCoefficientRealMean M)

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientRationalRealMean_invariant (M : InvariantMean G) (g : G) :
    (smallCoefficientRationalRealMean M).comp (smallCoefficientRationalAction g) =
      smallCoefficientRationalRealMean M := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q b
  change q • smallCoefficientRealMean M (g • b) = q • smallCoefficientRealMean M b
  rw [smallCoefficientRealMean_invariant]

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientRealCoinvariantMean (M : InvariantMean G) :
    Coinvariants (smallCoefficientRationalAction (G := G)) →ₗ[ℚ] ℝ :=
  Coinvariants.lift _ (smallCoefficientRationalRealMean M)
    (smallCoefficientRationalRealMean_invariant M)

set_option synthInstance.maxHeartbeats 400000 in
@[simp]
theorem smallCoefficientRealCoinvariantMean_one (M : InvariantMean G) :
    smallCoefficientRealCoinvariantMean M
      (Coinvariants.mk smallCoefficientRationalAction
        ((1 : ℚ) ⊗ₜ[ℤ] (1 : SmallCoefficientRing G))) = 1 := by
  change (1 : ℚ) • smallCoefficientRealMean M 1 = 1
  rw [smallCoefficientRealMean_one, one_smul]

set_option synthInstance.maxHeartbeats 400000 in
theorem exists_smallCoefficient_rational_mean (M : InvariantMean G) :
    ∃ m : SmallCoefficientRationalSpace (G := G) →ₗ[ℚ] ℚ,
      m ((1 : ℚ) ⊗ₜ[ℤ] (1 : SmallCoefficientRing G)) = 1 ∧
      ∀ (g : G) (x : SmallCoefficientRationalSpace (G := G)),
        m (smallCoefficientRationalAction g x) = m x := by
  let u := Coinvariants.mk smallCoefficientRationalAction
    ((1 : ℚ) ⊗ₜ[ℤ] (1 : SmallCoefficientRing G))
  have hu : u ≠ 0 := by
    intro h
    have hm := smallCoefficientRealCoinvariantMean_one M
    change smallCoefficientRealCoinvariantMean M u = 1 at hm
    rw [h, map_zero] at hm
    exact zero_ne_one hm
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ hu
  refine ⟨f.comp (Coinvariants.mk smallCoefficientRationalAction), hf, ?_⟩
  intro g x
  change f (Coinvariants.mk smallCoefficientRationalAction (smallCoefficientRationalAction g x)) =
    f (Coinvariants.mk smallCoefficientRationalAction x)
  rw [Coinvariants.mk_self_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordChartLeftShift
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact changes of basepoint in nilpotent exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Module LieModule
open scoped Manifold

variable {L E G W I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

/-- Coordinates use the given global exponential chart and the actual
chosen basis; no topology on the abstract Lie algebra is needed. -/
def exponentialCoordinates {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (b : Basis (Fin n) ℝ L) : (Fin n → ℝ) ≃ₜ G :=
  (b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart

omit [IsTopologicalGroup G] in
@[simp] theorem exponentialCoordinates_apply {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (b : Basis (Fin n) ℝ L) (z : Fin n → ℝ) :
    exponentialCoordinates e chart b z = chart (e (b.equivFun.symm z)) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegerExtensionHomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Top homology of an infinite cyclic extension

Tensoring the explicit mapping-cone resolution reduces the top degree to the
kernel of the induced translation difference on subgroup homology.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)
  [IsCyclic (G ⧸ q.ker)] [Infinite (G ⧸ q.ker)]
  (P : ProjectiveResolution (trivialIntegral q.ker)) (A : Rep ℤ G)

local instance instCommGroupQuotientSubgroupKerMultiplicativeInt_solutions_1_r0160bc_1 : CommGroup (G ⧸ q.ker) := IsCyclic.commGroup
def integerExtensionTensorMap :=
  (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (integerExtensionMap q t P)

def integerExtensionHomologyKernelIso (i : ℕ)
    (hN : IsZero (groupHomology (Rep.res q.ker.subtype A) (i + 1))) :
    groupHomology A (i + 1) ≅
      kernel (HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) i) := by
  classical
  let F := (Rep.coinvariantsTensor ℤ G).obj A
  have hz : IsZero
      (((quotientInducedResolution q.ker P).complex.coinvariantsTensorObj A).homology (i + 1)) :=
    IsZero.of_iso hN (inducedResolutionHomologyIso q.ker A P (i + 1))
  exact groupHomologyIso A (i + 1) (integerExtensionResolution q t ht P) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (i + 1)).mapIso
      (homotopyCofiber.mapHomologicalComplexObjIso (integerExtensionMap q t P) F) ≪≫
    cofiberChainHomologyKernelIso (integerExtensionTensorMap q t P A) i hz

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CyclicInvariantTopHomology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed top class lifts across an infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
variable {G : Type} [Group G]

theorem integerExtensionTensorMap_zero (q : G →* Multiplicative ℤ)
    [IsCyclic (G ⧸ q.ker)] (t : G) (A : Rep ℤ G) (d : ℕ)
    (ha : normalHomologyMap ℤ q.ker A d t⁻¹ = 𝟙 _) :
    HomologicalComplex.homologyMap
      (integerExtensionTensorMap q t (Rep.barResolution ℤ q.ker) A) d = 0 := by
  classical
  let F := ((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)
  let C := (quotientInducedResolution q.ker (Rep.barResolution ℤ q.ker)).complex
  let B : C ⟶ C := inducedBarTranslation q.ker t
  let E := inducedBarHomologyIso q.ker A d
  have hB : HomologicalComplex.homologyMap (F.map B) d = 𝟙 _ := by
    apply (cancel_mono E.hom).mp
    have he := inducedBarHomologyIso_translation q.ker A t d
    rw [ha, Category.comp_id] at he
    exact he.trans (Category.id_comp E.hom).symm
  have h := (((Rep.coinvariantsTensor ℤ G).obj A).mapHomotopy
    (integerExtensionBarHomotopy (t := t) q)).homologyMap_eq d
  change HomologicalComplex.homologyMap
      (integerExtensionTensorMap q t (Rep.barResolution ℤ q.ker) A) d =
    HomologicalComplex.homologyMap (F.map (B - 𝟙 C)) d at h
  rw [F.map_sub, F.map_id, HomologicalComplex.homologyMap_sub,
    HomologicalComplex.homologyMap_id, hB, sub_self] at h
  exact h

def cyclicInvariantTopHomologyIso (q : G →* Multiplicative ℤ)
    (t : G) (ht : q t = Multiplicative.ofAdd 1) (A : Rep ℤ G) (d : ℕ)
    (hv : IsZero (groupHomology (Rep.res q.ker.subtype A) (d + 1)))
    (ha : normalHomologyMap ℤ q.ker A d t⁻¹ = 𝟙 _) :
    groupHomology A (d + 1) ≅ groupHomology (Rep.res q.ker.subtype A) d := by
  classical
  letI := integerQuotient_isCyclic q t ht
  letI := integerQuotient_infinite q t ht
  let P := Rep.barResolution ℤ q.ker
  have hz := integerExtensionTensorMap_zero q t A d ha
  let E : kernel (HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) d) ≅
      ((normalInducedResolution ℤ q.ker P).complex.coinvariantsTensorObj A).homology d := by
    rw [hz]
    exact kernelZeroIsoSource
  exact integerExtensionHomologyKernelIso q t ht P A d hv ≪≫ E ≪≫
    inducedBarHomologyIso q.ker A d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CyclicTopHomologyInjection
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top homology injection for an infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2

def cyclicTopHomologyInjection {G : Type} [Group G]
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (P : ProjectiveResolution (trivialIntegral q.ker)) (A : Rep ℤ G) (d : ℕ)
    (hvanish : IsZero (groupHomology (Rep.res q.ker.subtype A) (d + 1))) :
    groupHomology A (d + 1) ⟶ groupHomology (Rep.res q.ker.subtype A) d := by
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  exact (integerExtensionHomologyKernelIso q t ht P A d hvanish).hom ≫
    kernel.ι (HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) d) ≫
      (inducedResolutionHomologyIso q.ker A P d).hom

instance cyclicTopHomologyInjection_mono {G : Type} [Group G]
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (P : ProjectiveResolution (trivialIntegral q.ker)) (A : Rep ℤ G) (d : ℕ)
    (hvanish : IsZero (groupHomology (Rep.res q.ker.subtype A) (d + 1))) :
    Mono (cyclicTopHomologyInjection q t ht P A d hvanish) := by
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  apply (ModuleCat.mono_iff_injective _).mpr
  let E := integerExtensionHomologyKernelIso q t ht P A d hvanish
  let F := inducedResolutionHomologyIso q.ker A P d
  let k := kernel.ι (HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) d)
  have hE : Function.Injective E.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hF : Function.Injective F.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hk : Function.Injective k := (ModuleCat.mono_iff_injective _).mp inferInstance
  exact hF.comp (hk.comp hE)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteGroupSyzygyScalar
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending a stable scalar through an integral split syzygy sequence -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

instance normalizedFreeRepresentation_integral_projective (A : Rep.{0} ℤ G) :
    Module.Projective ℤ (normalizedFreeRepresentation A) := by
  change Module.Projective ℤ ({a : A // a ≠ 0} →₀ ℤ[G])
  infer_instance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedSyzygyIteration
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving one normalized syzygy across an iterated syzygy -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedSyzygy_iterate_comm (n : ℕ) :
    (normalizedSyzygyFunctor (G := G)) ⋙ iteratedNormalizedSyzygy n =
      iteratedNormalizedSyzygy (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change normalizedSyzygyFunctor ⋙ (iteratedNormalizedSyzygy n ⋙ normalizedSyzygyFunctor) =
      iteratedNormalizedSyzygy (n + 1) ⋙ normalizedSyzygyFunctor
    rw [← Functor.assoc, ih]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteSumCompleteVanishing
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete cohomology of finite sums of vanishing coefficients -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G ι : Type} [Group G]

def integralRepresentationSumProjection (A : ι → Rep.{0} ℤ G) (i : ι) :
    integralRepresentationSum A ⟶ A i :=
  Rep.ofHom ⟨DirectSum.component ℤ ι (fun i => (A i).V) i, fun g => by
    apply LinearMap.ext
    intro x
    rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FinsuppCompleteVanishing
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_inclusion _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constant-family direct sum form of a countable coefficient sum -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule Finsupp.module
variable {G : Type} [Group G]

def finsuppIntegralSumIso (A : Rep.{0} ℤ G) (ι : Type) :
    A.finsupp ι ≅ integralRepresentationSum (fun _ : ι => A) := by
  classical
  refine Rep.mkIso (ρ := A.ρ.finsupp ι)
    (σ := Representation.directSum (fun _ : ι => A.ρ))
    (Representation.Equiv.mk (finsuppLequivDFinsupp ℤ) ?_)
  intro g
  apply Finsupp.lhom_ext'
  intro i
  ext a
  simp [Representation.finsupp_single, Representation.directSum, finsuppLequivDFinsupp]
  rename_i j
  by_cases h : i = j <;> simp [h]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_TopHomologyNaturality
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient naturality of top-dimensional duality

Use one fixed resolution comparison for all coefficients. This records the
naturality needed to turn a coefficient trace into a top-homology trace.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem tensor_top_d_zero
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hbound : IsZero (P.complex.X (n + 1))) (A : Rep ℤ G) :
    (P.complex.coinvariantsTensorObj A).d (n + 1) n = 0 := by
  change ((Rep.coinvariantsTensor ℤ G).obj A).map (P.complex.d (n + 1) n) = 0
  rw [hbound.eq_of_src (P.complex.d (n + 1) n) 0, Functor.map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AdjointMatrixHeight
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic diagonal characters of the actual adjoint action -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

def matrixLogDiagonalHom {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℝ)
    (hupper : ∀ g, (ρ g).IsUpperTriangular) (hpos : ∀ g i, 0 < ρ g i i) :
    G →* Multiplicative (Fin n → ℝ) where
  toFun g := Multiplicative.ofAdd (fun i => Real.log (ρ g i i))
  map_one' := by
    apply Multiplicative.ext
    funext i
    simp
  map_mul' g h := by
    apply Multiplicative.ext
    funext i
    change Real.log (ρ (g * h) i i) = Real.log (ρ g i i) + Real.log (ρ h i i)
    rw [map_mul, triangular_mul_diag _ _ (hupper g) (hupper h),
      Real.log_mul (hpos g i).ne' (hpos h i).ne']

@[simp] theorem matrixLogDiagonalHom_apply {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℝ) (hupper) (hpos) (g : G) (i : Fin n) :
    (matrixLogDiagonalHom ρ hupper hpos g).toAdd i = Real.log (ρ g i i) := rfl

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSupportLegs
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support legs in the actual Cartan subgroup

The canonical height section gives a one-parameter subgroup realizing any
height displacement. Its continuity follows from the published faithful
exponential representation, and its height traces the exact affine segment.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)

variable [SimplyConnectedSpace G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G))
  [H.IsCartanSubalgebra]
  {W : Type*}
  [NormedAddCommGroup W]
  [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The actual Cartan direction of a height displacement. -/
def supportLegDirection (w₀ w₁ : W) : H :=
  cartanHeightSection T H (eW.symm (w₁ - w₀))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectProductTopology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The product topology on the Cartan semidirect cover -/

noncomputable section
namespace PolycyclicRecognition

variable {N D : Type*} [Group N] [Group D] [TopologicalSpace N] [TopologicalSpace D]
  (φ : D →* MulAut N)

attribute [local instance] semidirectProductTopology

theorem continuous_semidirect_inl :
    Continuous (SemidirectProduct.inl : N → N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

instance instLocallyCompactSpaceSemidirectProduct_solutions [LocallyCompactSpace N] [LocallyCompactSpace D] :
    LocallyCompactSpace (N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).locallyCompactSpace_iff.mpr inferInstance

instance instSecondCountableTopologySemidirectProduct_solutions [SecondCountableTopology N] [SecondCountableTopology D] :
    SecondCountableTopology (N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).secondCountableTopology

instance instConnectedSpaceSemidirectProduct_solutions [ConnectedSpace N] [ConnectedSpace D] : ConnectedSpace (N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).symm.surjective.connectedSpace
    (semidirectProductHomeomorph φ).symm.continuous

variable [IsTopologicalGroup N] [IsTopologicalGroup D]

theorem semidirectProductTopologicalGroup
    (hφ : Continuous (fun p : D × N => φ p.1 p.2)) : IsTopologicalGroup (N ⋊[φ] D) where
  continuous_mul := by
    apply continuous_induced_rng.2
    exact ((continuous_semidirect_left φ).comp continuous_fst |>.mul
      (hφ.comp (((continuous_semidirect_right φ).comp continuous_fst).prodMk
        ((continuous_semidirect_left φ).comp continuous_snd)))).prodMk
      (((continuous_semidirect_right φ).comp continuous_fst).mul
        ((continuous_semidirect_right φ).comp continuous_snd))
  continuous_inv := by
    apply continuous_induced_rng.2
    exact (hφ.comp ((continuous_semidirect_right φ).inv.prodMk
      (continuous_semidirect_left φ).inv)).prodMk (continuous_semidirect_right φ).inv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactSemidirectModel
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact semidirect extensions used by the model comparison -/

noncomputable section
namespace PolycyclicRecognition
open Set

variable {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]
  (α : K →* MulAut G)
attribute [local instance] semidirectProductTopology

theorem compactlyGenerated_compact_semidirect [CompactSpace K]
    (hG : ∃ U : Set G, IsCompact U ∧ Subgroup.closure U = ⊤) :
    ∃ U : Set (G ⋊[α] K), IsCompact U ∧ Subgroup.closure U = ⊤ := by
  obtain ⟨U,hU,hgen⟩ := hG
  let V := (SemidirectProduct.inl '' U : Set (G ⋊[α] K)) ∪ SemidirectProduct.inr '' univ
  refine ⟨V, (hU.image (continuous_semidirect_inl α)).union
    (isCompact_univ.image (continuous_semidirect_inr α)), ?_⟩
  apply top_unique
  intro p _
  have hn : p.left ∈ (Subgroup.closure V).comap (SemidirectProduct.inl : G →* G ⋊[α] K) := by
    have ht : (⊤ : Subgroup G) ≤ (Subgroup.closure V).comap SemidirectProduct.inl := by
      rw [← hgen]
      refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      exact Subgroup.subset_closure (Or.inl ⟨g,hg,rfl⟩)
    exact ht (Subgroup.mem_top _)
  have hk : SemidirectProduct.inr p.right ∈ Subgroup.closure V :=
    Subgroup.subset_closure (Or.inr ⟨p.right,mem_univ _,rfl⟩)
  convert (Subgroup.closure V).mul_mem hn hk using 1
  all_goals try with_reducible_and_instances rfl
  exact (SemidirectProduct.inl_left_mul_inr_right p).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConstructMinimizingLieMetric
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the proper minimizing metric on the Lie model -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] [LocallyCompactSpace G]

def leftRiemannianMinimizingMetric (e : E ≃L[ℝ] F) : ProperMinimizingMetric G where
  metric := leftRiemannianMetric (G := G) e
  topology_eq := leftRiemannianMetric_topology e
  proper := leftRiemannianMetric_proper e
  leftInvariant := leftRiemannianMetric_isometric e
  minimizing := by
    let metric := leftRiemannianMetric (G := G) e
    let proper := leftRiemannianMetric_proper (G := G) e
    intro g
    exact exists_metric_segment (leftRiemannianMetric_approximateMidpoints e) 1 g

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialQuotientSection
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected pure-word section in actual exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V J EN EQ N Q : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype J]
  [AddCommGroup EN] [Module ℝ EN] [TopologicalSpace EN]
  [IsTopologicalAddGroup EN] [ContinuousSMul ℝ EN]
  [AddCommGroup EQ] [Module ℝ EQ] [TopologicalSpace EQ] [T2Space EQ]
  [IsTopologicalAddGroup EQ] [ContinuousSMul ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace N] [TopologicalSpace Q] [Group N] [Group Q]
  (U : LieIdeal ℝ V) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)
  (eN : V ≃ₗ[ℝ] EN) (eQ : (V ⧸ U.toSubmodule) ≃ₗ[ℝ] EQ)
  (chartN : EN ≃ₜ N) (chartQ : EQ ≃ₜ Q)

omit [Fintype J] in
include hlift in
/-- Naturality of the actual quotient exponential proves that this is a
right inverse of the group quotient. -/
theorem exponentialQuotientSection_rightInverse (π : N →* Q)
    (hπ : ∀ v, π (chartN (eN v)) = chartQ (eQ (U.toSubmodule.mkQ v))) :
    ∀ q, π (exponentialQuotientSection U bQ lift eN eQ chartN chartQ q) = q := by
  intro q
  obtain ⟨v, rfl⟩ := chartQ.surjective q
  obtain ⟨v, rfl⟩ := eQ.surjective v
  rw [exponentialQuotientSection_apply, hπ, quotientLinearSection_rightInverse U bQ lift hlift]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GradedFlowLimit
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convergence of horizontal flows in graded coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Filter Set Module
open scoped Topology

variable {n : ℕ}

/-- Right multiplication along the exponential line with velocity `v`,
recorded jointly in its base point and time. -/
def dynkinFlowMap {c : ℕ} (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (v : (Fin n → ℝ)) : C((Fin n → ℝ) × ℝ, (Fin n → ℝ)) :=
  ⟨fun z => dynkinProduct a B z.1 (z.2 • v),
    continuous_dynkinProduct a _ _ _ continuous_const continuous_fst
      (continuous_snd.smul continuous_const)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_HeightConjugationDifferential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The adjoint action is the identity on the canonical height quotient -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

def conjugationDifferentialLinearEquiv (g : G) :
    GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₗ[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G where
  __ := (conjugationDifferentialHom (E := E) g).toLinearMap
  invFun := conjugationDifferentialHom (E := E) g⁻¹
  left_inv v := by
    change (conjugationDifferentialHom (E := E) g⁻¹ *
      conjugationDifferentialHom (E := E) g) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    change (conjugationDifferentialHom (E := E) g *
      conjugationDifferentialHom (E := E) g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IndependentWeightCone
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The closed cones used by the neighboring-offset argument

A ray and a cone on two independent weights are closed. We construct them
as actual proper cones, so polar separation requires no closedness input.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {I : Type*} [Fintype I]

@[simp] theorem mem_closedWeightRay {α : V} (hα : α ≠ 0) (β : V) :
    β ∈ closedWeightRay α hα ↔ ∃ c : ℝ, 0 ≤ c ∧ β = c • α := by
  simp only [closedWeightRay, mem_independentWeightCone, Fin.sum_univ_one]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a 0, ha 0, he.symm⟩
  · rintro ⟨c, hc, he⟩
    exact ⟨fun _ => c, fun _ => hc, he.symm⟩

@[simp] theorem mem_closedTwoWeightCone (α η : V) (h : LinearIndependent ℝ ![α, η])
    (β : V) : β ∈ closedTwoWeightCone α η h ↔
      ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ β = c • α + d • η := by
  simp only [closedTwoWeightCone, mem_independentWeightCone, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a 0, a 1, ha 0, ha 1, he.symm⟩
  · rintro ⟨c, d, hc, hd, he⟩
    refine ⟨![c, d], ?_, he.symm⟩
    intro i
    fin_cases i <;> assumption

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NetSmoothing
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly close Lipschitz interpolation of coarse maps -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal BigOperators

variable {X Y : Type*} [Group X] [MetricSpace X] [ProperSpace X]
  [IsIsometricSMul X X] [MetricSpace Y]
  {V : Set X} (hV : V.Pairwise (fun x y => 1 < dist x y)) [LinearOrder V]

def netSmoothedMap (c : ControlledContraction Y) (p₀ : Y) (f : X → Y) (x : X) : Y :=
  finiteSupportCenter c p₀ (fun v : V => f v) (unitNetPartition hV x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormalizedWeightRays
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deduplicating positive weight rays

Unit normalization gives a concrete finite set of positive rays, even when
the original generator list repeats some rays with different multiplicities.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

instance instFiniteNormalizedWeightRays (α : I → W →L[ℝ] ℝ) : Finite (NormalizedWeightRays α) :=
  (Set.finite_range _).to_subtype

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RepresentedExponentialDifferential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exponential differential in a faithful Lie representation

Left translation identifies this differential with the average of the
negative adjoint flow. A real triangular adjoint basis makes that average
invertible, independently of a global exponential chart.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance instNormedAddCommGroup_solutions : NormedAddCommGroup L := generatorConjugationNormedAddCommGroup
local instance instNormedSpaceReal_solutions : NormedSpace ℝ L := generatorConjugationNormedSpace

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_CartanNilshadow
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent Lie algebra attached to the Cartan height action

The graph of minus the semisimple height action is a Lie subalgebra of the
affine derivation algebra. Its first coordinate is linearly the original Lie
algebra, while its bracket has the semisimple action removed.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
def cartanNilshadowEquiv : L ≃ₗ[ℝ] CartanNilshadow T H where
  toFun x := ⟨⟨x, -heightSemisimpleAction T H x⟩, rfl⟩
  invFun p := p.val.left
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · exact p.property.symm
  map_add' x y := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · change -heightSemisimpleAction T H (x + y) =
        -heightSemisimpleAction T H x + -heightSemisimpleAction T H y
      rw [map_add, neg_add]
  map_smul' r x := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · change -heightSemisimpleAction T H (r • x) = r • -heightSemisimpleAction T H x
      rw [map_smul, smul_neg]

set_option maxHeartbeats 1000000 in
instance : FiniteDimensional ℝ (CartanNilshadow T H) :=
  (cartanNilshadowEquiv T H).finiteDimensional

set_option maxHeartbeats 1000000 in
theorem cartanNilshadow_bracket (x y : L) :
    (cartanNilshadowEquiv T H).symm ⁅cartanNilshadowEquiv T H x,
      cartanNilshadowEquiv T H y⁆ =
      ⁅x, y⁆ - heightSemisimpleAction T H x y + heightSemisimpleAction T H y x := by
  change ⁅x, y⁆ + (-heightSemisimpleAction T H x) y -
    (-heightSemisimpleAction T H y) x = _
  simp only [LieDerivation.neg_apply]
  abel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowWeightAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original solvable algebra as an extension of its nilshadow -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H
local notation "σ" => heightSemisimpleAction T H
local notation "e" => cartanNilshadowEquiv T H

theorem heightSemisimpleAction_apply_commute (x y z : L) : σ x (σ y z) = σ y (σ x z) := by
  have h := DFunLike.congr_fun (heightSemisimpleAction_commute T H x y) z
  exact sub_eq_zero.mp h

theorem cartanNilshadow_bracket_symm (p q : K) :
    (e).symm ⁅p, q⁆ = ⁅(e).symm p, (e).symm q⁆ - σ ((e).symm p) ((e).symm q) +
      σ ((e).symm q) ((e).symm p) := by
  obtain ⟨x, rfl⟩ := (e).surjective p
  obtain ⟨y, rfl⟩ := (e).surjective q
  simpa only [LinearEquiv.symm_apply_apply] using cartanNilshadow_bracket T H x y

theorem semisimple_derives_nilshadow_bracket (x y z : L) :
    σ x (⁅y, z⁆ - σ y z + σ z y) =
      (⁅y, σ x z⁆ - σ y (σ x z) + σ (σ x z) y) +
      (⁅σ x y, z⁆ - σ (σ x y) z + σ z (σ x y)) := by
  simp only [map_add, map_sub, LieDerivation.apply_lie_eq_add,
    heightSemisimpleAction_annihilate, LieDerivation.zero_apply, sub_zero, add_zero]
  rw [heightSemisimpleAction_apply_commute T H x y z,
    heightSemisimpleAction_apply_commute T H x z y]
  abel

def nilshadowWeightOperator (x : L) : K →ₗ[ℝ] K :=
  (e).toLinearMap.comp ((σ x).toLinearMap.comp (e).symm.toLinearMap)

@[simp]
theorem nilshadowWeightOperator_symm (x : L) (p : K) :
    (e).symm (nilshadowWeightOperator T H x p) = σ x ((e).symm p) :=
  (e).symm_apply_apply _

def nilshadowWeightDerivation (x : L) : LieDerivation ℝ K K where
  toLinearMap := nilshadowWeightOperator T H x
  leibniz' p q := by
    rw [← lie_skew q (nilshadowWeightOperator T H x p), sub_neg_eq_add]
    apply (e).symm.injective
    rw [map_add, nilshadowWeightOperator_symm, cartanNilshadow_bracket_symm,
      cartanNilshadow_bracket_symm, cartanNilshadow_bracket_symm,
      nilshadowWeightOperator_symm, nilshadowWeightOperator_symm]
    exact semisimple_derives_nilshadow_bracket T H x ((e).symm p) ((e).symm q)

@[simp]
theorem nilshadowWeightDerivation_symm (x : L) (p : K) :
    (e).symm (nilshadowWeightDerivation T H x p) = σ x ((e).symm p) :=
  nilshadowWeightOperator_symm T H x p

def nilshadowWeightAction : L →ₗ⁅ℝ⁆ LieDerivation ℝ K K where
  toFun := nilshadowWeightDerivation T H
  map_add' x y := by
    apply LieDerivation.ext
    intro p
    apply (e).symm.injective
    simp only [LieDerivation.add_apply, map_add, nilshadowWeightDerivation_symm,
      LieDerivation.add_apply]
  map_smul' r x := by
    apply LieDerivation.ext
    intro p
    apply (e).symm.injective
    simp only [LieDerivation.smul_apply, map_smul, nilshadowWeightDerivation_symm,
      RingHom.id_apply, LieDerivation.smul_apply]
  map_lie' {x y} := by
    apply LieDerivation.ext
    intro p
    apply (e).symm.injective
    simp only [LieDerivation.lie_apply, map_sub, nilshadowWeightDerivation_symm,
      heightSemisimpleAction_lie, LieDerivation.zero_apply,
      heightSemisimpleAction_apply_commute T H x y, sub_self]

def nilshadowSemidirectEmbedding :
    L →ₗ⁅ℝ⁆ K ⋊⁅(nilshadowWeightAction T H).range.incl⁆ (nilshadowWeightAction T H).range where
  toFun x := ⟨e x, (nilshadowWeightAction T H).rangeRestrict x⟩
  map_add' x y := by
    apply SemiDirectSum.ext
    · exact (e).map_add x y
    · exact map_add _ _ _
  map_smul' r x := by
    apply SemiDirectSum.ext
    · exact (e).map_smul r x
    · exact map_smul _ _ _
  map_lie' {x y} := by
    apply SemiDirectSum.ext
    · apply (e).symm.injective
      change (e).symm (e ⁅x, y⁆) = (e).symm (⁅e x, e y⁆ +
        nilshadowWeightDerivation T H x (e y) - nilshadowWeightDerivation T H y (e x))
      rw [LinearEquiv.symm_apply_apply, map_sub, map_add,
        cartanNilshadow_bracket, nilshadowWeightDerivation_symm,
        nilshadowWeightDerivation_symm, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply]
      abel
    · exact LieHom.map_lie _ x y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularLocalLogarithm
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local logarithm in the full real upper triangular algebra -/

noncomputable section
namespace PolycyclicRecognition

open Filter Topology
open scoped Matrix.Norms.Operator

instance instIsTopologicalRingRealTriangularAlgebra (n : ℕ) : IsTopologicalRing (RealTriangularAlgebra n) :=
  IsTopologicalSemiring.toIsTopologicalRing inferInstance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightChambers
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incident weight chambers determine an extreme ray

Both signs of every active hyperplane occur among genuine open chambers.
Intersecting their closures therefore imposes the active equations; actual
extremality, rather than a rank assumption, identifies the resulting ray.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Finite I]

def weightChamber (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : Set W :=
  {w | ∀ i, 0 < orientedWeight α σ i w}

def incidentWeightChamber (α : I → W →L[ℝ] ℝ) (w : W) (σ : I → Bool) : Prop :=
  (weightChamber α σ).Nonempty ∧ w ∈ closedWeightChamber α σ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedChainMetric
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A proper chain metric from a compact generating neighborhood -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped Pointwise NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  (K : Set G) (hK : Subgroup.closure K = ⊤)
  (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K)
  (hbounded : ∀ x y : G, dist x y ≤ 1)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (hball : ∀ g : G, dist 1 g ≤ δ → g ∈ K)

local notation "N" => compactWeightedNorm K hK hbounded hsymm

include hbounded in
theorem metric_le_weightedDistance (x y : G) : dist x y ≤ N (x⁻¹ * y) := by
  have h := seminorm_le_weightedWordNorm (compactWordCost K hK)
    (metricGroupNorm (G := G)).toGroupSeminorm (metric_le_compactWordCost K hK hbounded)
    (x⁻¹ * y)
  change dist 1 (x⁻¹ * y) ≤ N (x⁻¹ * y) at h
  simpa only [dist_one_groupDifference] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegralLatticePowerIndex
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-index powers in an integral vector lattice -/

noncomputable section
namespace PolycyclicRecognition

def latticeCoordinateHom (n : ℕ) (i : Fin n) : IntegralLatticeGroup n →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (z.toAdd i)
  map_one' := rfl
  map_mul' _ _ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeNormalFlag
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normal cyclic flag of a lattice quotient -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] {r : ℕ} (q : G →* IntegralLatticeGroup r)

def latticeNormalFlag (i : ℕ) : Subgroup G where
  carrier := {g | ∀ j : Fin r, i ≤ j.val → (q g).toAdd j = 0}
  one_mem' := by intro j _; rw [q.map_one]; rfl
  mul_mem' := by
    intro a b ha hb j hj
    rw [map_mul]
    change (q a).toAdd j + (q b).toAdd j = 0
    rw [ha j hj, hb j hj, add_zero]
  inv_mem' := by
    intro a ha j hj
    rw [map_inv]
    change -(q a).toAdd j = 0
    rw [ha j hj, neg_zero]

instance latticeNormalFlag_normal (i : ℕ) : (latticeNormalFlag q i).Normal where
  conj_mem x hx g := by
    intro j hj
    rw [q.map_mul, q.map_mul, q.map_inv]
    change (q g).toAdd j + (q x).toAdd j + -(q g).toAdd j = 0
    rw [hx j hj]
    abel

def latticeNormalFlagStep (i : Fin r) :
    latticeNormalFlag q (i.val + 1) →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd ((q (g : G)).toAdd i)
  map_one' := by change Multiplicative.ofAdd ((q 1).toAdd i) = 1; rw [q.map_one]; rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change (q ((a : G) * (b : G))).toAdd i = (q (a : G)).toAdd i + (q (b : G)).toAdd i
    rw [map_mul]
    rfl

end PolycyclicRecognition

end

end OAI
end


