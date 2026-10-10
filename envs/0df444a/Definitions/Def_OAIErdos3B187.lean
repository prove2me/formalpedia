-- Prove2me | Definitions.Def_OAIErdos3B187
-- name    : OAIErdos3B187
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T07:40:29.683851+00:00
-- url     : https://prove2.me/theorems/f9257eba-45b1-43e5-9c12-5d3707f1ff11
-- title:
--   OpenAI Erdős-3 split, definitions bundle 188 of 197
-- statement:
--   Definitions bundle 188 of 197 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B186`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 188 available.
--
--   Modules: `OAI.Erdos3.FixedDensity.HasTaoBundleCountingStep`, `OAI.Erdos3.FixedDensity.HypergraphBundle.BaseEdgeWeight`, `OAI.Erdos3.FixedDensity.HypergraphBundle.BaseWeightsIdempotent`, `OAI.Erdos3.FixedDensity.HypergraphBundle.BaseWeightsInUnitInterval`, `OAI.Erdos3.FixedDensity.HypergraphBundle.DoubledEdgeSource`, `OAI.Erdos3.FixedDensity.HypergraphBundle.DoubledOccurrenceVertex`, `OAI.Erdos3.FixedDensity.HypergraphBundle.EdgeComplement`, `OAI.Erdos3.FixedDensity.HypergraphBundle.HasOrderedConfigurationBundleFrozenCutRepresentation`, `OAI.Erdos3.FixedDensity.HypergraphBundle.HasOrderedConfigurationBundleFrozenUniformity`, `OAI.Erdos3.FixedDensity.HypergraphBundle.HasOrderedConfigurationBundleLocalizedDefect`, `OAI.Erdos3.FixedDensity.HypergraphBundle.IsClosedUnderInclusion`, `OAI.Erdos3.FixedDensity.HypergraphBundle.WeightsIdempotent`, `OAI.Erdos3.FixedDensity.HypergraphBundle.WeightsInUnitInterval`, `OAI.Erdos3.FixedDensity.HypergraphBundle.WeightsInUnitInterval.eraseEdge`, `OAI.Erdos3.FixedDensity.HypergraphBundle.ambientPositiveFaceOfProperSubface`, `OAI.Erdos3.FixedDensity.HypergraphBundle.ambientPositiveFaceOfProperSubface_rank`, `OAI.Erdos3.FixedDensity.HypergraphBundle.bundleCount`, `OAI.Erdos3.FixedDensity.HypergraphBundle.bundleMainProduct`, `OAI.Erdos3.FixedDensity.HypergraphBundle.bundleMainProduct_filterEdges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.bundleMainProduct_lowerOrder`, `OAI.Erdos3.FixedDensity.HypergraphBundle.bundleMainProduct_strictBoundary`, `OAI.Erdos3.FixedDensity.HypergraphBundle.bundleProduct`, `OAI.Erdos3.FixedDensity.HypergraphBundle.card_doubledEdge`, `OAI.Erdos3.FixedDensity.HypergraphBundle.casesOn`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledAssignment`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledAssignment_lift_false`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledAssignment_lift_true`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledBundleEdgeFactor`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledEdge`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledEdgeOfSource`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledEdges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledProjection`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledProjection_lift`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledRemainderMoment`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledSourceProduct`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledVertexForget`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledVertexForget_lift`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledVertexLift`, `OAI.Erdos3.FixedDensity.HypergraphBundle.doubledVertexLift_injective`, `OAI.Erdos3.FixedDensity.HypergraphBundle.duplicateOutside`, `OAI.Erdos3.FixedDensity.HypergraphBundle.duplicateOutside_edges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.duplicateOutside_projection`, `OAI.Erdos3.FixedDensity.HypergraphBundle.edgeContribution`, `OAI.Erdos3.FixedDensity.HypergraphBundle.edgeRemainder`, `OAI.Erdos3.FixedDensity.HypergraphBundle.edgeRemainderAverage`, `OAI.Erdos3.FixedDensity.HypergraphBundle.edgeRemainderFiber`, `OAI.Erdos3.FixedDensity.HypergraphBundle.edgeSumEquiv`, `OAI.Erdos3.FixedDensity.HypergraphBundle.edgeTuple`, `OAI.Erdos3.FixedDensity.HypergraphBundle.edgeTuple_splitEdgeEquiv_symm`, `OAI.Erdos3.FixedDensity.HypergraphBundle.eraseEdge`, `OAI.Erdos3.FixedDensity.HypergraphBundle.eraseEdge_edges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.exists_selectedVertex_not_mem_of_mem_erase`, `OAI.Erdos3.FixedDensity.HypergraphBundle.extendConfigurationFaceTuple`, `OAI.Erdos3.FixedDensity.HypergraphBundle.extendConfigurationFaceTuple_projection`, `OAI.Erdos3.FixedDensity.HypergraphBundle.filterEdges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.filterEdges_edges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.filterEdges_projection`, `OAI.Erdos3.FixedDensity.HypergraphBundle.finsetMembershipEquivOfEq`, `OAI.Erdos3.FixedDensity.HypergraphBundle.finsetMembershipEquivOfEq_symm_val`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenBundleFaceTupleEquiv`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenBundleFaceTupleEquiv_apply`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenBundleFaceTupleEquiv_symm_apply`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenBundleInsertedAssignment`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenBundleInsertedSelectedTuple`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenBundleMissingCoordinate`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenBundleMissingVertex`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenBundleRemainderCutTest`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenEdgeCorrelation`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenOccurrenceOrderEquiv`, `OAI.Erdos3.FixedDensity.HypergraphBundle.frozenProjectedEdgeOrderIso`, `OAI.Erdos3.FixedDensity.HypergraphBundle.image_doubledProjection_doubledEdge`, `OAI.Erdos3.FixedDensity.HypergraphBundle.image_forget_doubledEdge`, `OAI.Erdos3.FixedDensity.HypergraphBundle.liftProjectedSubedge`, `OAI.Erdos3.FixedDensity.HypergraphBundle.lowerExteriorMainProduct`, `OAI.Erdos3.FixedDensity.HypergraphBundle.lowerOrder`, `OAI.Erdos3.FixedDensity.HypergraphBundle.lowerOrder_edges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.maximalRemainderMainProduct`, `OAI.Erdos3.FixedDensity.HypergraphBundle.mem_doubledEdge`, `OAI.Erdos3.FixedDensity.HypergraphBundle.mem_doubledEdges_iff`, `OAI.Erdos3.FixedDensity.HypergraphBundle.mem_filterEdges_edges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.mem_lowerOrder_edges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.mem_orderedConfigurationStrictFaceFamily`, `OAI.Erdos3.FixedDensity.HypergraphBundle.mem_strictBoundary_edges`, `OAI.Erdos3.FixedDensity.HypergraphBundle.order`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationBundleDefect`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationBundleFace`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationBundleFaceState`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationBundleFaceTarget`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationBundleFaceTuple`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationBundleFaceTupleEquiv`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationBundleFaceTupleEquiv_apply`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationBundleLocalizedDefect`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationBundleUniform`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedConfigurationStrictFaceFamily`, `OAI.Erdos3.FixedDensity.HypergraphBundle.orderedFaceTuple_extendConfigurationFaceTuple`, `OAI.Erdos3.FixedDensity.HypergraphBundle.projectedEdgeOrderIso`, `OAI.Erdos3.FixedDensity.HypergraphBundle.projectedEdgeOrderIso_apply_val`, `OAI.Erdos3.FixedDensity.HypergraphBundle.projectedEdgeTuple`, `OAI.Erdos3.FixedDensity.HypergraphBundle.projectedEdge_card_le`, `OAI.Erdos3.FixedDensity.HypergraphBundle.projectedEdge_nonempty`, `OAI.Erdos3.FixedDensity.HypergraphBundle.projectionEquiv`, `OAI.Erdos3.FixedDensity.HypergraphBundle.projectionEquiv_apply_val`, `OAI.Erdos3.FixedDensity.HypergraphBundle.pullbackBaseEdgeWeight`, `OAI.Erdos3.FixedDensity.HypergraphBundle.pullbackBaseEdgeWeight_of_mem`, `OAI.Erdos3.FixedDensity.HypergraphBundle.restrictEdgeTuple`, `OAI.Erdos3.FixedDensity.HypergraphBundle.restrictEdgeTuple_edgeTuple`, `OAI.Erdos3.FixedDensity.HypergraphBundle.splitDoubledAssignmentEquiv`, `OAI.Erdos3.FixedDensity.HypergraphBundle.splitDoubledAssignmentEquiv_symm_apply`, `OAI.Erdos3.FixedDensity.HypergraphBundle.splitEdgeEquiv`, `OAI.Erdos3.FixedDensity.HypergraphBundle.splitEdgeEquiv_fst`, `OAI.Erdos3.FixedDensity.HypergraphBundle.strictBoundary`, `OAI.Erdos3.FixedDensity.HypergraphBundle.strictBoundaryLocalProduct`, `OAI.Erdos3.FixedDensity.HypergraphBundle.strictBoundary_edges`, `OAI.Erdos3.FixedDensity.IsBundleCountingEnvelope.casesOn`, `OAI.Erdos3.FixedDensity.bundleCommonEnvelopeError`, `OAI.Erdos3.FixedDensity.bundleCommonEnvelopeError_succ_order`, `OAI.Erdos3.FixedDensity.bundleCommonEnvelopeError_zero_order`, `OAI.Erdos3.FixedDensity.bundleCommonEnvelopeError_zero_parameter`, `OAI.Erdos3.FixedDensity.bundleCommonNextRow`, `OAI.Erdos3.FixedDensity.bundleCommonNextRow_succ`, `OAI.Erdos3.FixedDensity.bundleCommonNextRow_zero`, `OAI.Erdos3.FixedDensity.bundleCommonNextRow_zero_parameter`, `OAI.Erdos3.FixedDensity.bundleCommonStepIncrement`, `OAI.Erdos3.FixedDensity.bundleCountingStepIncrement`, `OAI.Erdos3.FixedDensity.empty_mem_orderedConfigurationBaseEdges`, `OAI.Erdos3.FixedDensity.mem_orderedConfigurationBaseEdges_iff`, `OAI.Erdos3.FixedDensity.mem_positiveOrderedFaceEdge`, `OAI.Erdos3.FixedDensity.orderedConfigurationBaseDensity`, `OAI.Erdos3.FixedDensity.orderedConfigurationBaseDensity_empty`, `OAI.Erdos3.FixedDensity.orderedConfigurationBaseDensity_positiveOrderedFaceEdge`, `OAI.Erdos3.FixedDensity.orderedConfigurationBaseEdges`, `OAI.Erdos3.FixedDensity.orderedConfigurationBaseWeight`, `OAI.Erdos3.FixedDensity.orderedConfigurationBaseWeight_empty`, `OAI.Erdos3.FixedDensity.orderedConfigurationBaseWeight_positiveOrderedFaceEdge`, `OAI.Erdos3.FixedDensity.orderedConfigurationEdgeTuple`, `OAI.Erdos3.FixedDensity.orderedConfigurationInitialBundle`, `OAI.Erdos3.FixedDensity.orderedConfigurationInitialBundle_edges`, `OAI.Erdos3.FixedDensity.orderedConfigurationInitialBundle_projection`, `OAI.Erdos3.FixedDensity.positiveOrderedFaceEdge`, `OAI.Erdos3.FixedDensity.positiveOrderedFaceEdge_card`, `OAI.Erdos3.FixedDensity.positiveOrderedFaceEdge_card_le`, `OAI.Erdos3.FixedDensity.positiveOrderedFaceEdge_injective`, `OAI.Erdos3.FixedDensity.positiveOrderedFaceEdge_nonempty`, `OAI.Erdos3.FixedDensity.positiveOrderedFaceEdge_ofEdge`, `OAI.Erdos3.FixedDensity.positiveOrderedFaceEdge_orderIsoOfFin_val`, `OAI.Erdos3.FixedDensity.positiveOrderedFaceOfEdge`, `OAI.Erdos3.FixedDensity.positiveOrderedFaceOfEdge_edge`, `OAI.Erdos3.FixedDensity.sourceBundleRemovalCountThreshold`, `OAI.Erdos3.FixedDensity.sourceBundleRemovalDensityBudget`, `OAI.Erdos3.FixedDensity.sourceBundleRemovalHorizon`, `OAI.Erdos3.FixedDensity.sourceBundleRemovalKappa`, `OAI.Erdos3.FixedDensity.sourceBundleRemovalStep`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialGroupMap_weightedAdaptedRealChartHom`, `OAI.Erdos3.VectorPolynomial.PreparedFiniteForwardSlot`, `OAI.Erdos3.VectorPolynomial.PreparedFiniteScheduleGeometryPrescribedScaleStatement`, `OAI.Erdos3.VectorPolynomial.PreparedFiniteScheduleGeometryStatement`, `OAI.Erdos3.VectorPolynomial.PreparedUniformDegreeComparison`, `OAI.Erdos3.VectorPolynomial.PreparedUniformDegreeDirectScalarBounds`, `OAI.Erdos3.VectorPolynomial.PreparedUniformDegreeGeometryAt`, `OAI.Erdos3.VectorPolynomial.exists_canonicalSliceEarlyScale_budget`, `OAI.Erdos3.VectorPolynomial.exists_commonRadius_densityCap_uniform_bound`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleEarlyBudget`, `OAI.Erdos3.VectorPolynomial.exists_preparedUniformDegreeEarlyBudget`, `OAI.Erdos3.VectorPolynomial.exists_preparedUniformDegreePrecisionBudget`, `OAI.Erdos3.VectorPolynomial.exists_preparedUniformEarlyRadius`, `OAI.Erdos3.VectorPolynomial.exists_prepared_commonRadius_densityCap_forward_bound`, `OAI.Erdos3.VectorPolynomial.exists_prepared_commonRadius_densityCap_nested_bound`, `OAI.Erdos3.VectorPolynomial.exists_primitiveCanonicalSliceEarlyScale_budget`, `OAI.Erdos3.VectorPolynomial.forecastFrozenIntegerMixedValue`, `OAI.Erdos3.VectorPolynomial.forecastLawCenteredRecoveredKernel`, `OAI.Erdos3.VectorPolynomial.forecastLawRecoveredKernel`, `OAI.Erdos3.VectorPolynomial.forecastLawRecoveredRationalFactor`, `OAI.Erdos3.VectorPolynomial.forecastRecoveredIntegerLabels`, `OAI.Erdos3.VectorPolynomial.le_lowTaggedSubspaceFamily`, `OAI.Erdos3.VectorPolynomial.lowTaggedCoordinates`, `OAI.Erdos3.VectorPolynomial.lowTaggedCoordinates_apply_slot`, `OAI.Erdos3.VectorPolynomial.lowTaggedCoordinates_mem_iff`, `OAI.Erdos3.VectorPolynomial.lowTaggedCoordinates_mem_iff_low`, `OAI.Erdos3.VectorPolynomial.lowTaggedCoordinates_projection`, `OAI.Erdos3.VectorPolynomial.lowTaggedCoordinates_projection_eq_zero`, `OAI.Erdos3.VectorPolynomial.lowTaggedPolynomial_centered_residueAffine_homogeneousComponent`, `OAI.Erdos3.VectorPolynomial.lowTaggedPolynomial_residueAffine`, `OAI.Erdos3.VectorPolynomial.lowTaggedSubspaceFamily`, `OAI.Erdos3.VectorPolynomial.lowTaggedSubspaceFamily_span`, `OAI.Erdos3.VectorPolynomial.lowTaggedTopPolynomial_centered_residueAffine`, `OAI.Erdos3.VectorPolynomial.lowTaggedTopPolynomial_residueAffine_coeff_mem_iSup`, `OAI.Erdos3.VectorPolynomial.mem_lowTaggedSubspaceFamily_iff`, `OAI.Erdos3.VectorPolynomial.preparedCommonRadiusDensityCapNestedExponent`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardDetectionSlot`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardDetectionSlot_degree`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardModelSlot`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardModelSlot_degree`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardSlotDegree`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardSlot_card`, `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDirectCoarse`, `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDirectMaster`, `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleLocalMaster`, `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleLocalPhysical`, `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeDirectLate`, `OAI.Erdos3.VectorPolynomial.preparedUniformEarlyRadius_eighth`, `OAI.Erdos3.VectorPolynomial.prepared_commonRadius_densityCap_nested_bound`, `OAI.Erdos3.exists_finiteSupport_rationalGridLift`, `OAI.Erdos3.exists_finite_normalized_real_grid_corrections`, `OAI.Erdos3.normalizedRealGridCorrectionSolutions`, `OAI.Erdos3.twice_chartCoefficient_le_exp`, `_private.Dynamics.PreparedFiniteScheduleGeometryBudget.0.OAI.Erdos3.VectorPolynomial.canonical_derivativeAxis_mono`, `_private.Dynamics.PreparedFiniteScheduleGeometryBudget.0.OAI.Erdos3.VectorPolynomial.canonical_inverseAxis_mono`, `_private.Dynamics.PreparedFiniteScheduleGeometryBudget.0.OAI.Erdos3.VectorPolynomial.canonical_jointSource_mono`, `_private.Dynamics.PreparedFiniteScheduleGeometryBudget.0.OAI.Erdos3.VectorPolynomial.canonical_minorConstant_mono`, `_private.Dynamics.PreparedFiniteScheduleGeometryBudget.0.OAI.Erdos3.VectorPolynomial.canonical_minorDegree_mono`, `_private.Dynamics.PreparedFiniteScheduleGeometryBudget.0.OAI.Erdos3.VectorPolynomial.canonical_minorLog_mono`, `_private.Dynamics.PreparedFiniteScheduleGeometryBudget.0.OAI.Erdos3.VectorPolynomial.canonical_minorVariable_mono`, `_private.Dynamics.PreparedFiniteScheduleGeometryBudget.0.OAI.Erdos3.VectorPolynomial.canonical_profileInput_mono`, `_private.Dynamics.PreparedFiniteScheduleGeometryBudget.0.OAI.Erdos3.VectorPolynomial.canonical_weightAxis_mono`, `_private.Probability.PreparedCommonRadiusDensityCapNested.0.OAI.Erdos3.VectorPolynomial.exists_commonRadius_densityCap_bound`, `_private.Sampling.FiniteNormalizedRealGridCorrection.0.OAI.Erdos3.normalizedChartCorrectionSolutions_map`, `_private.Sampling.ForecastLawCenteredRecoveredKernel.0.OAI.Erdos3.VectorPolynomial.centeredTagPullback`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B147
import Definitions.Def_OAIErdos3B185

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LowTaggedAffineCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

theorem lowTaggedPolynomial_residueAffine (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (q : ℕ) (r : X → ℤ)
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedPolynomial J d (fun j => residueAffine q r (poly j)) i =
      residueAffinePolynomial q r (lowTaggedPolynomial J d poly i) := by
  apply MvPolynomial.funext
  intro x
  rw [lowTaggedPolynomial_eval, eval_residueAffine,
    residueAffinePolynomial_eval_real, lowTaggedPolynomial_eval]

theorem lowTaggedPolynomial_centered_residueAffine_homogeneousComponent (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (q : ℕ) (r : X → ℤ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    homogeneousComponent (lowTaggedWeight J d i)
        (residueAffinePolynomial q r (lowTaggedPolynomial J d poly i - C (c i))) =
      homogeneousComponent (lowTaggedWeight J d i)
        (lowTaggedPolynomial J d (fun j => residueAffine q r (poly j)) i) := by
  rw [lowTaggedPolynomial_residueAffine]
  have hc : homogeneousComponent (lowTaggedWeight J d i) (C (c i) : MvPolynomial X ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simpa using lowTaggedWeight_pos J d i
  simp only [residueAffinePolynomial, map_sub, eval₂Hom_C, hc, sub_zero]

theorem lowTaggedTopPolynomial_centered_residueAffine (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (q : ℕ) (r : X → ℤ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :
    ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
        (fun i => homogeneousComponent (lowTaggedWeight J d i)
          (residueAffinePolynomial q r (lowTaggedPolynomial J d poly i - C (c i)))) =
      lowTaggedTopPolynomial J d (fun j => residueAffine q r (poly j)) := by
  unfold lowTaggedTopPolynomial
  congr 1
  funext i
  exact lowTaggedPolynomial_centered_residueAffine_homogeneousComponent J d poly q r c i

theorem lowTaggedTopPolynomial_residueAffine_coeff_mem_iSup (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (q : ℕ) (r : X → ℤ) (α : X →₀ ℕ) :
    coefficients (lowTaggedTopPolynomial J d (fun j => residueAffine q r (poly j))) α ∈
      ⨆ h : Fin d, lowTaggedRetained J d W h :=
  lowTaggedTopPolynomial_coeff_mem_iSup J d (fun j => residueAffine q r (poly j)) W
    (fun j β hβ => coefficients_residueAffine_nonzero_mem (W j) q r (poly j)
      (hcoeff j) β hβ) α

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LowTaggedCoordinateProjection
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedCoordinates (d : ℕ) (x : ∀ j, J j → ℝ) :
    Fin (Fintype.card (LowTaggedIndex J d)) → ℝ :=
  fun i => x (lowTaggedIndex J d i).1 (lowTaggedIndex J d i).2

@[simp] theorem lowTaggedCoordinates_apply_slot (d : ℕ) (x : ∀ j, J j → ℝ)
    (j : Fin m) (hj : j.val + 1 ≤ d) (k : J j) :
    lowTaggedCoordinates J d x (lowTaggedSlot J d j hj k) = x j k := by
  unfold lowTaggedCoordinates
  rw [lowTaggedIndex_slot]

theorem lowTaggedCoordinates_projection (d : ℕ) (x : ∀ j, J j → ℝ)
    (j : Fin m) (hj : j.val + 1 ≤ d) :
    basisGradeProjection (Pi.basisFun ℝ _) (lowTaggedWeight J d) (j.val + 1)
        (lowTaggedCoordinates J d x) =
      lowTaggedEmbedding J d j hj (x j) := by
  classical
  funext i
  rw [pi_basisGradeProjection_apply]
  by_cases hi : (lowTaggedIndex J d i).1 = j
  · obtain ⟨k, hk⟩ := lowTaggedSlot_eq_of_tag J d j hj i hi
    subst i
    simp [lowTaggedWeight]
  · have hweight : lowTaggedWeight J d i ≠ j.val + 1 := by
      intro he
      apply hi
      apply Fin.ext
      unfold lowTaggedWeight at he
      omega
    rw [if_neg hweight, lowTaggedEmbedding_apply_of_ne J d j hj _ i hi]

theorem lowTaggedCoordinates_projection_eq_zero (d : ℕ) (x : ∀ j, J j → ℝ)
    (h : ℕ) (hm : m ≤ h) :
    basisGradeProjection (Pi.basisFun ℝ _) (lowTaggedWeight J d) (h + 1)
      (lowTaggedCoordinates J d x) = 0 := by
  classical
  funext i
  rw [pi_basisGradeProjection_apply]
  have hweight : lowTaggedWeight J d i ≠ h + 1 := by
    have hi := (lowTaggedIndex J d i).1.isLt
    unfold lowTaggedWeight
    omega
  simp only [hweight, ite_false, Pi.zero_apply]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowTaggedGradedSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedSubspaceFamily (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (j : Fin m) : Submodule ℝ (J j → ℝ) :=
  if hj : j.val + 1 ≤ d then K.comap (lowTaggedEmbedding J d j hj) else ⊤

theorem mem_lowTaggedSubspaceFamily_iff (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (j : Fin m) (hj : j.val + 1 ≤ d) (x : J j → ℝ) :
    x ∈ lowTaggedSubspaceFamily J d K j ↔ lowTaggedEmbedding J d j hj x ∈ K := by
  simp only [lowTaggedSubspaceFamily, dif_pos hj, Submodule.mem_comap]

theorem le_lowTaggedSubspaceFamily (d : ℕ)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hUK : ∀ h : Fin d, lowTaggedRetained J d U h ≤ K) (j : Fin m) :
    U j ≤ lowTaggedSubspaceFamily J d K j := by
  intro x hx
  by_cases hj : j.val + 1 ≤ d
  · rw [mem_lowTaggedSubspaceFamily_iff J d K j hj]
    let h : Fin d := ⟨j.val, by omega⟩
    apply hUK h
    have heq : lowTaggedRetained J d U h =
        (U j).map (lowTaggedEmbedding J d j hj) := by
      simp only [lowTaggedRetained, h, dif_pos j.isLt]
    rw [heq]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  · simp only [lowTaggedSubspaceFamily, dif_neg hj, Submodule.mem_top]

theorem lowTaggedCoordinates_mem_iff (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) K)
    (x : ∀ j, J j → ℝ) :
    lowTaggedCoordinates J d x ∈ K ↔ ∀ j, x j ∈ lowTaggedSubspaceFamily J d K j := by
  constructor
  · intro hx j
    by_cases hj : j.val + 1 ≤ d
    · rw [mem_lowTaggedSubspaceFamily_iff J d K j hj]
      rw [← lowTaggedCoordinates_projection J d x j hj]
      exact hK (j.val + 1) _ hx
    · simp only [lowTaggedSubspaceFamily, dif_neg hj, Submodule.mem_top]
  · intro hx
    rw [← sum_positive_coordinate_grades (lowTaggedWeight J d) d
      (lowTaggedWeight_pos J d) (lowTaggedWeight_le J d) (lowTaggedCoordinates J d x)]
    apply Submodule.sum_mem
    intro h _
    by_cases hm : h.val < m
    · let j : Fin m := ⟨h.val, hm⟩
      have hj : j.val + 1 ≤ d := by exact Nat.succ_le_of_lt h.isLt
      have hjmem := (mem_lowTaggedSubspaceFamily_iff J d K j hj (x j)).mp (hx j)
      rw [lowTaggedCoordinates_projection J d x j hj]
      exact hjmem
    · rw [lowTaggedCoordinates_projection_eq_zero J d x h.val (Nat.le_of_not_gt hm)]
      exact K.zero_mem

theorem lowTaggedCoordinates_mem_iff_low (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) K)
    (x : ∀ j, J j → ℝ) :
    lowTaggedCoordinates J d x ∈ K ↔
      ∀ j, j.val + 1 ≤ d → x j ∈ lowTaggedSubspaceFamily J d K j := by
  rw [lowTaggedCoordinates_mem_iff J d K hK x]
  constructor
  · exact fun hx j _ => hx j
  · intro hx j
    by_cases hj : j.val + 1 ≤ d
    · exact hx j hj
    · simp only [lowTaggedSubspaceFamily, dif_neg hj, Submodule.mem_top]

theorem lowTaggedSubspaceFamily_span {A : Type*} (d : ℕ)
    (g : A → Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (hg : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d)
      (Submodule.span ℝ (Set.range g)))
    (j : Fin m) (hj : j.val + 1 ≤ d) :
    lowTaggedSubspaceFamily J d (Submodule.span ℝ (Set.range g)) j =
      Submodule.span ℝ (Set.range (fun a k => g a (lowTaggedSlot J d j hj k))) := by
  rw [lowTaggedSubspaceFamily, dif_pos hj]
  exact lowTagged_comap_span_eq J d j hj g hg

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteNormalizedRealGridCorrection
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem exists_finiteSupport_rationalGridLift {V : Type*}
    (S : Finset (V →₀ ℕ)) (P : MvPolynomial V ℝ) (q : ℕ)
    (hsupport : P.support ⊆ S)
    (hgrid : ∀ α : V →₀ ℕ, ∃ z : ℤ, P.coeff α = (z : ℝ) / (q : ℝ)) :
    ∃ r : MvPolynomial V ℚ, r.support ⊆ S ∧
      (∀ α : V →₀ ℕ, ∃ z : ℤ, r.coeff α = (z : ℚ) / (q : ℚ)) ∧
      MvPolynomial.map (Rat.castHom ℝ) r = P := by
  classical
  let z : S → ℤ := fun α => Classical.choose (hgrid α.val)
  let c : S → ℚ := fun α => (z α : ℚ) / (q : ℚ)
  let r := polynomialOfFiniteCoefficientVector S c
  have hcoeff (α : S) : r.coeff α.val = c α :=
    polynomialOfFiniteCoefficientVector_coeff S c α
  have hzero (α : V →₀ ℕ) (hα : α ∉ S) : r.coeff α = 0 :=
    polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem S c α hα
  refine ⟨r, polynomialOfFiniteCoefficientVector_support_subset S c, ?_, ?_⟩
  · intro α
    by_cases hα : α ∈ S
    · exact ⟨z ⟨α, hα⟩, hcoeff ⟨α, hα⟩⟩
    · refine ⟨0, ?_⟩
      rw [hzero α hα]
      simp only [Int.cast_zero, zero_div]
  · ext α
    rw [MvPolynomial.coeff_map]
    by_cases hα : α ∈ S
    · rw [hcoeff ⟨α, hα⟩]
      change (Rat.castHom ℝ) ((z ⟨α, hα⟩ : ℚ) / (q : ℚ)) = P.coeff α
      simp only [map_div₀, map_intCast, map_natCast]
      exact (Classical.choose_spec (hgrid α)).symm
    · rw [hzero α hα, map_zero]
      exact (MvPolynomial.notMem_support_iff.mp (fun h => hα (hsupport h))).symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U V : Type*}

def normalizedRealGridCorrectionSolutions
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ) :
    Set (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℝ) :=
  {sr | sr.1.support ⊆ S ∧ sr.2.support ⊆ S ∧
    (∀ α, |sr.1.coeff α| ≤ B) ∧
    (∀ α, ∃ z : ℤ, sr.2.coeff α = (z : ℝ) / q) ∧
    P = aeval (R := ℝ) (normalizedRealPolynomialChart H A) sr.1 + sr.2}

theorem normalizedChartCorrectionSolutions_map
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ)
    (sr : MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ)
    (hsr : sr ∈ normalizedChartCorrectionSolutions H A S P B q) :
    (sr.1, MvPolynomial.map (Rat.castHom ℝ) sr.2) ∈
      normalizedRealGridCorrectionSolutions H A S P B q := by
  refine ⟨hsr.1, (support_map_subset (Rat.castHom ℝ) sr.2).trans hsr.2.1,
    hsr.2.2.1, ?_, hsr.2.2.2.2⟩
  intro α
  obtain ⟨z, hz⟩ := hsr.2.2.2.1 α
  refine ⟨z, ?_⟩
  rw [coeff_map, hz]
  simp

theorem exists_finite_normalized_real_grid_corrections
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ S.card ∧
      ∃ candidate : Fin m → (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℝ),
        (∀ j, candidate j ∈ normalizedRealGridCorrectionSolutions H A S P B q) ∧
        ∀ sr, sr ∈ normalizedRealGridCorrectionSolutions H A S P B q →
          ∃ j, candidate j = sr := by
  obtain ⟨m, hm, candidate, hvalid, hcomplete⟩ :=
    exists_finite_normalized_chart_corrections H hH A S P B hB q hq
  refine ⟨m, hm, (fun j => ((candidate j).1,
    MvPolynomial.map (Rat.castHom ℝ) (candidate j).2)), ?_, ?_⟩
  · intro j
    exact normalizedChartCorrectionSolutions_map H A S P B q (candidate j) (hvalid j)
  · intro sr hsr
    obtain ⟨r, hrsupport, hrgrid, hrmap⟩ :=
      exists_finiteSupport_rationalGridLift S sr.2 q hsr.2.1 hsr.2.2.2.1
    have hr : (sr.1, r) ∈ normalizedChartCorrectionSolutions H A S P B q := by
      refine ⟨hsr.1, hrsupport, hsr.2.2.1, hrgrid, ?_⟩
      rw [hrmap]
      exact hsr.2.2.2.2
    obtain ⟨j, hj⟩ := hcomplete (sr.1, r) hr
    refine ⟨j, ?_⟩
    change ((candidate j).1, MvPolynomial.map (Rat.castHom ℝ) (candidate j).2) = sr
    rw [hj]
    exact Prod.ext rfl hrmap

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceRelativeInitializerBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uα
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformEarlyRadius (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {p g : ℝ}, 0 ≤ p → 0 ≤ g →
      let pRadius := allocatedCommonProductRadiusLog m p g
      let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m p g
      pRadius ∈ Set.Icc 0 ((p + g + A) ^ A) ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      ∀ {G : Type uG} [Fintype G] {I : Fin m → Type uI} [∀ j, Fintype (I j)]
        {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {α : Type uα} [Fintype α] (rowSets : Fin m → Finset (Finset α))
        [∀ j, Nonempty (rowSets j)],
        Fintype.card α ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        let T := allocatedIdealCoverSupport (G := G) B rowSets
        let r := allocatedProductIdealSiteRadius (G := G) B rowSets
        1 ≤ r ∧ (∀ j, 0 ≤ T j) ∧
        (∀ j, partitionedIdealRadius α m + 1 ≤ T j) ∧
        (∀ j, (Fintype.card (BoundedCoefficientExponent
          (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
        (∀ j, (rowSets j).card * T j ≤ (r : ℝ)) ∧
        ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp g) →
          (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
          (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
          (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
            (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4) := by
  obtain ⟨A, hA, hbound⟩ := exists_allocatedCommonProductRadiusLog_bound m
  refine ⟨A, hA, ?_⟩
  intro p g hp hg pRadius R
  obtain ⟨hlog, hpos, hone, hinv, _⟩ := allocatedCommonProductRadius_bounds m hp hg
  refine ⟨⟨hlog, hbound hp hg⟩, fun _ => ⟨hpos, hone, hinv.le⟩, ?_⟩
  intro G _ I _ n B _ α _ rowSets _ hdim hvars hI hn
  dsimp only
  have hgeo := allocatedCanonicalSlice_source_geometry B rowSets hp hg hdim hvars hI hn
    (fun _ => 0) (fun _ => le_refl 0) (fun _ => Real.exp_nonneg g)
    (fun _ => hpos.le) (fun _ => le_refl (allocatedCommonProductRadius m p g))
  refine ⟨hgeo.1, hgeo.2.1, hgeo.2.2.1, hgeo.2.2.2.1, hgeo.2.2.2.2.1, ?_⟩
  intro C hC hCg
  have hgeometry := allocatedCanonicalSlice_source_geometry B rowSets hp hg hdim hvars hI hn
    C hC hCg (fun _ => hpos.le) (fun _ => le_refl (allocatedCommonProductRadius m p g))
  refine ⟨?_, hgeometry.2.2.2.2.2.1, hgeometry.2.2.2.2.2.2⟩
  intro j
  have hT : 1 ≤ allocatedIdealCoverSupport (G := G) B rowSets j := by
    linarith [hgeometry.2.2.1 j, partitionedIdealRadius_nonneg α m]
  calc
    _ = C j * (((Fintype.card (I j) : ℝ) + 1) * (1 * R j)) := by ring
    _ ≤ C j * (((Fintype.card (I j) : ℝ) + 1) *
        (allocatedIdealCoverSupport (G := G) B rowSets j * R j)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT hpos.le) (by positivity)) (hC j)
    _ ≤ _ := hgeometry.2.2.2.2.2.1 j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem twice_chartCoefficient_le_exp {C Pchart Bstruct : ℝ}
    (hC : C ≤ Real.exp Pchart) (hallow : Pchart + 1 ≤ Bstruct) :
    2 * C ≤ Real.exp Bstruct := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  calc
    2 * C ≤ 2 * Real.exp Pchart := mul_le_mul_of_nonneg_left hC (by norm_num)
    _ ≤ Real.exp 1 * Real.exp Pchart :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (Pchart + 1) := by rw [← Real.exp_add, add_comm]
    _ ≤ Real.exp Bstruct := Real.exp_le_exp.mpr hallow

namespace VectorPolynomial

theorem preparedUniformEarlyRadius_eighth
    {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
    [∀ j, Nonempty (rowSets j)] {p g Pchart : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hdim : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j, C j ≤ Real.exp Pchart) (hallow : Pchart + 1 ≤ g) :
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m p g
    let T := allocatedIdealCoverSupport (G := G) B rowSets
    let r := allocatedProductIdealSiteRadius (G := G) B rowSets
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 8) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 8) ∧
      (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 8) := by
  intro R T r
  obtain ⟨_, _, hfamilies⟩ :=
    (Classical.choose_spec (exists_preparedUniformEarlyRadius m)).2 hp hg
  have hgeometry := hfamilies (G := G) B rowSets hdim hvars hI hn
  have hsmall := hgeometry.2.2.2.2.2
  have hdoubled := hsmall (fun j => 2 * C j)
    (fun j => mul_nonneg (by norm_num) (hC j))
    (fun j => twice_chartCoefficient_le_exp (hchart j) hallow)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    nlinarith only [hdoubled.1 j]
  · intro j
    nlinarith only [hdoubled.2.1 j]
  · intro j
    nlinarith only [hdoubled.2.2 j]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

section Source
variable {X₀ J₀ : Type} {m : ℕ} (prep : RankPreparationFamily X₀ J₀ m) (nX M : ℕ)
local notation "Jalloc" => modularInitialBlockCount m (nX + m * M)

end Source
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteScheduleGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem canonical_minorVariable_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ D') :
    affineMinorVariableEnvelope D ≤ affineMinorVariableEnvelope D' := by
  have hD'0 := hD0.trans hD
  dsimp only [affineMinorVariableEnvelope]
  gcongr

theorem canonical_minorDegree_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ D') :
    affineMinorDegreeEnvelope D ≤ affineMinorDegreeEnvelope D' := by
  have hD'0 := hD0.trans hD
  dsimp only [affineMinorDegreeEnvelope]
  gcongr

theorem canonical_minorConstant_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ D') :
    affineMinorConstantEnvelope D ≤ affineMinorConstantEnvelope D' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hd := canonical_minorDegree_mono hD0 hD
  have hd0 := affineMinorDegreeEnvelope_nonneg hD0
  have hd'0 := affineMinorDegreeEnvelope_nonneg hD'0
  dsimp only [affineMinorConstantEnvelope]
  gcongr

theorem canonical_minorLog_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    affineMinorLogEnvelope D P E F ≤ affineMinorLogEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hd := canonical_minorDegree_mono hD0 hD
  have hc := canonical_minorConstant_mono hD0 hD
  have hv0 := affineMinorVariableEnvelope_nonneg hD0
  have hv'0 := affineMinorVariableEnvelope_nonneg hD'0
  have hd0 := affineMinorDegreeEnvelope_nonneg hD0
  have hd'0 := affineMinorDegreeEnvelope_nonneg hD'0
  have hc0 := affineMinorConstantEnvelope_nonneg hD0
  dsimp only [affineMinorLogEnvelope]
  gcongr

theorem canonical_inverseAxis_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    affineInverseAxisEnvelope D P E F ≤ affineInverseAxisEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hm := canonical_minorLog_mono hD0 hP0 hE0 hF0 hD hP hE hF
  dsimp only [affineInverseAxisEnvelope]
  gcongr

theorem canonical_derivativeAxis_mono {D D' P P' : ℝ}
    (hD0 : 0 ≤ D) (hD : D ≤ D') (hP : P ≤ P') :
    affineDerivativeAxisEnvelope D P ≤ affineDerivativeAxisEnvelope D' P' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  dsimp only [affineDerivativeAxisEnvelope]
  gcongr

theorem canonical_weightAxis_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    affineWeightAxisEnvelope D P E F ≤ affineWeightAxisEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hm := canonical_minorLog_mono hD0 hP0 hE0 hF0 hD hP hE hF
  dsimp only [affineWeightAxisEnvelope]
  gcongr

theorem canonical_jointSource_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    jointAffineSourceEnvelope D P E F ≤ jointAffineSourceEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hi := canonical_inverseAxis_mono hD0 hP0 hE0 hF0 hD hP hE hF
  have hd := canonical_derivativeAxis_mono hD0 hD hP
  have hw := canonical_weightAxis_mono hD0 hP0 hE0 hF0 hD hP hE hF
  have hv0 := affineMinorVariableEnvelope_nonneg hD0
  have hi0 := affineInverseAxisEnvelope_nonneg hD0 hP0 hE0 hF0
  have hd0 := affineDerivativeAxisEnvelope_nonneg hD0 hP0
  have hw0 := affineWeightAxisEnvelope_nonneg hD0 hP0 hE0 hF0
  dsimp only [jointAffineSourceEnvelope, jointAffineInverseEnvelope,
    jointAffineDerivativeEnvelope, jointAffineWeightEnvelope]
  gcongr

theorem canonical_profileInput_mono {D D' A A' T T' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hA0 : 0 ≤ A) (hT0 : 0 ≤ T) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hA : A ≤ A') (hT : T ≤ T') (hE : E ≤ E') (hF : F ≤ F') :
    affineProfileInputEnvelope D A T E F ≤ affineProfileInputEnvelope D' A' T' E' F' := by
  have hD'0 := hD0.trans hD
  apply canonical_jointSource_mono hD0
    (by dsimp only [affineProfileCoefficientEnvelope]; positivity) (by positivity) hF0 hD
  · dsimp only [affineProfileCoefficientEnvelope]; gcongr
  · gcongr
  · exact hF

theorem exists_canonicalSliceEarlyScale_budget (m s Cdetect : ℕ) (A T : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type*} [Fintype G] {count nX : ℕ}
      {P D p q a target Qstride pRadius : ℝ},
      0 ≤ P → D ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P → q ∈ Set.Icc 0 P →
      a ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      pRadius ∈ Set.Icc 0 P → (count : ℝ) ≤ P → (nX : ℝ) ≤ P →
      (Fintype.card G : ℝ) ≤ P →
      let gainLog := slicedDetectionGainLog s Cdetect count p q a
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
      let F := p + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (A : ℝ) (T : ℝ) E F
      let Pscale := pRadius + Ptail
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
      let budget := (P + C) ^ C
      P ≤ budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧
      Tmod ∈ Set.Icc 0 budget ∧ Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget := by
  obtain ⟨Adet, _, hdet⟩ := exists_slicedDetection_uniform_budget s Cdetect
  let Ac : ℕ := ⌈(A : ℝ)⌉₊
  let Tc : ℕ := ⌈(T : ℝ)⌉₊
  let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
  let X : Polynomial ℕ := Polynomial.X
  let detPoly := (4 * X + Polynomial.C Adet) ^ Adet
  let errorPoly := X + X * (Polynomial.C (m * 2 ^ (m + 1)) * detPoly) + 5
  let inputPoly := affineProfileInputEnvelope X (Polynomial.C Ac) (Polynomial.C Tc) errorPoly (X + 2)
  let rhoPoly := 2 * inputPoly + 2
  let tailPoly := affineProfileToleranceEnvelope m X (X * (X + 1) + X * X + X + 1)
    (Polynomial.C Ac) (Polynomial.C Tc) errorPoly (X + 2)
  let modPoly := Polynomial.C (m + 1) * detPoly + X * X
  let scalePoly := (X + (X + tailPoly) + rhoPoly + detPoly + X + (X + 2) + modPoly + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (X + detPoly + rhoPoly + tailPoly + modPoly + (X + tailPoly) + scalePoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P D p q a target Qstride pRadius hP hD hp hq ha ht hQs hRadius hc hnX hG
    gainLog Pk F Tmod E Prho Ptail Pscale K' scaleLog budget
  let detBound := (4 * P + Adet) ^ Adet
  let errorBound := P + P * ((m * 2 ^ (m + 1) : ℕ) * detBound) + 5
  let inputBound := affineProfileInputEnvelope P (Ac : ℝ) (Tc : ℝ) errorBound (P + 2)
  let rhoBound := 2 * inputBound + 2
  let tailBound := affineProfileToleranceEnvelope m P (P * (P + 1) + P * P + P + 1)
    (Ac : ℝ) (Tc : ℝ) errorBound (P + 2)
  let modBound := ((m + 1 : ℕ) : ℝ) * detBound + P * P
  let scaleBound := (P + (P + tailBound) + rhoBound + detBound + P + (P + 2) + modBound + K) ^ K
  have hD0 := hD.1
  have hp0 := hp.1
  have hq0 := hq.1
  have ha0 := ha.1
  have ht0 := ht.1
  have hQs0 := hQs.1
  have hRadius0 := hRadius.1
  have hgain0 : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s Cdetect count hp0 hq0 ha0
  have hk0 : 0 ≤ Pk := by dsimp only [Pk]; rw [scalarKernelLogarithmicBudget_eq]; positivity
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hinput0 : 0 ≤ affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F :=
    jointAffineSourceEnvelope_nonneg hD0
      (by dsimp [affineProfileCoefficientEnvelope]; positivity) (by positivity) hF0
  have hrho0 : 0 ≤ Prho := by dsimp only [Prho]; positivity
  have htail0 : 0 ≤ Ptail := by dsimp only [Ptail, affineProfileToleranceEnvelope, affineProfileCoefficientEnvelope]; positivity
  have hmod0 : 0 ≤ Tmod := by dsimp only [Tmod]; positivity
  have hscaleP0 : 0 ≤ Pscale := add_nonneg hRadius0 htail0
  have hscale0 : 0 ≤ scaleLog := by dsimp only [scaleLog]; positivity
  have hdet := hdet (G := G) hP hp0 hq0 ha0 hc hG
  have hdetPow : (P + p + q + a + Adet) ^ Adet ≤ detBound := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hp.2, hq.2, ha.2]
  have hgain : gainLog ≤ detBound := hdet.1.trans hdetPow
  have hk : Pk ≤ detBound := hdet.2.trans hdetPow
  have hAc : (A : ℝ) ≤ Ac := Nat.le_ceil _
  have hTc : (T : ℝ) ≤ Tc := Nat.le_ceil _
  have hdet0 : 0 ≤ detBound := by dsimp only [detBound]; positivity
  have herror0 : 0 ≤ errorBound := by dsimp only [errorBound]; positivity
  have hinputBound0 : 0 ≤ inputBound := jointAffineSourceEnvelope_nonneg hP
    (by dsimp [affineProfileCoefficientEnvelope]; positivity) (by positivity) (by positivity)
  have hrhoBound0 : 0 ≤ rhoBound := by dsimp only [rhoBound]; positivity
  have htailBound0 : 0 ≤ tailBound := by dsimp only [tailBound, affineProfileToleranceEnvelope, affineProfileCoefficientEnvelope]; positivity
  have hmodBound0 : 0 ≤ modBound := by dsimp only [modBound]; positivity
  have hscaleBound0 : 0 ≤ scaleBound := by dsimp only [scaleBound]; positivity
  have hE : E ≤ errorBound := by dsimp only [E, errorBound]; gcongr; exact ht.2; exact hD.2
  have hF : F ≤ P + 2 := by dsimp only [F]; linarith only [hp.2]
  have hinput : affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F ≤ inputBound :=
    canonical_profileInput_mono hD0 A.coe_nonneg T.coe_nonneg hE0 hF0 hD.2 hAc hTc hE hF
  have hrho : Prho ≤ rhoBound := by dsimp only [Prho, rhoBound]; gcongr
  have htail : Ptail ≤ tailBound := by
    dsimp only [Ptail, tailBound, affineProfileToleranceEnvelope, affineProfileCoefficientEnvelope]
    gcongr
    all_goals first | exact hinput | exact hD.2
  have hmod : Tmod ≤ modBound := by dsimp only [Tmod, modBound]; gcongr; exact hQs.2
  have hscaleP : Pscale ≤ P + tailBound := add_le_add hRadius.2 htail
  have hscale : scaleLog ≤ scaleBound := by
    dsimp only [scaleLog, scaleBound]
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    all_goals first | exact hD.2 | exact ht.2
  have hsum : P + detBound + rhoBound + tailBound + modBound + (P + tailBound) + scaleBound ≤ budget := by
    simpa [X, detPoly, errorPoly, inputPoly, rhoPoly, tailPoly, modPoly, scalePoly,
      detBound, errorBound, inputBound, rhoBound, tailBound, modBound, scaleBound,
      affineProfileInputEnvelope, affineProfileCoefficientEnvelope, affineProfileToleranceEnvelope,
      jointAffineSourceEnvelope, jointAffineInverseEnvelope, jointAffineDerivativeEnvelope,
      jointAffineWeightEnvelope, affineInverseAxisEnvelope, affineDerivativeAxisEnvelope,
      affineWeightAxisEnvelope, affineMinorLogEnvelope, affineMinorVariableEnvelope,
      affineMinorDegreeEnvelope, affineMinorConstantEnvelope, Polynomial.eval₂_pow] using hbound P hP
  refine ⟨?_, ⟨hgain0, ?_⟩, ⟨hk0, ?_⟩, ⟨hrho0, ?_⟩, ⟨htail0, ?_⟩,
    ⟨hmod0, ?_⟩, ⟨hscaleP0, ?_⟩, ⟨hscale0, ?_⟩⟩ <;>
    linarith only [hsum, hP, hgain, hk, hrho, htail, hmod, hscaleP, hscale,
      hdet0, hrhoBound0, htailBound0, hmodBound0, hscaleBound0]

theorem exists_primitiveCanonicalSliceEarlyScale_budget (m s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type*} [Fintype G] {count nX : ℕ}
      {P pnum p q a target Qstride pRadius : ℝ},
      0 ≤ P → pnum ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P → q ∈ Set.Icc 0 P →
      a ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      pRadius ∈ Set.Icc 0 P → (count : ℝ) ≤ P → (nX : ℝ) ≤ P →
      (Fintype.card G : ℝ) ≤ P →
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect count p q a
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
      let F := p + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let Pscale := pRadius + Ptail
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
      let budget := (P + C) ^ C
      P ≤ budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧
      Tmod ∈ Set.Icc 0 budget ∧ Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget := by
  obtain ⟨Aearly, _, hearly⟩ := exists_canonicalSliceEarlyScale_budget m s Cdetect
    canonicalSublevelCutoffLip canonicalTransitionLip
  let X : Polynomial ℕ := Polynomial.X
  let poly := (allocatedComparisonDimension m X + Polynomial.C Aearly) ^ Aearly
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P pnum p q a target Qstride pRadius hP hnum hp hq ha ht hQs hRadius hc hnX hG
    D gainLog Pk F Tmod E Prho Ptail Pscale K scaleLog budget
  let R := allocatedComparisonDimension m P
  have hR0 : 0 ≤ R := (allocatedComparisonDimension_bounds m hP).1
  have hPR : P ≤ R := (allocatedComparisonDimension_bounds m hP).2.2.1
  have hnum0 := hnum.1
  have hD0 : 0 ≤ D := (allocatedComparisonDimension_bounds m hnum0).1
  have hDR : D ≤ R := by
    dsimp only [D, R, allocatedComparisonDimension]
    gcongr <;> exact hnum.2
  have hlift {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 R :=
    ⟨hx.1, hx.2.trans hPR⟩
  have hbudget : (R + Aearly) ^ Aearly ≤ budget := by
    simpa [poly, X, R, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound P hP
  obtain ⟨hbase, hgain, hk, hrho, htail, hmod, hscaleP, hscale⟩ :=
    hearly (G := G) hR0 ⟨hD0, hDR⟩ (hlift hp) (hlift hq) (hlift ha) (hlift ht)
      (hlift hQs) (hlift hRadius) (hc.trans hPR) (hnX.trans hPR) (hG.trans hPR)
  have hbudgetLift {x : ℝ} (hx : x ∈ Set.Icc 0 ((R + Aearly) ^ Aearly)) :
      x ∈ Set.Icc 0 budget := ⟨hx.1, hx.2.trans hbudget⟩
  exact ⟨hPR.trans (hbase.trans hbudget), ⟨hD0, hDR.trans (hbase.trans hbudget)⟩,
    hbudgetLift hgain, hbudgetLift hk, hbudgetLift hrho, hbudgetLift htail,
    hbudgetLift hmod, hbudgetLift hscaleP, hbudgetLift hscale⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleEarlyBudget
    (m nStages Cmax : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
      {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Qstride : ℝ}
      (pDetect aDetect target : K → ℝ),
      Fintype.card K ≤ nStages → (∀ k, degree k ≤ m) → (∀ k, Cdetect k ≤ Cmax) →
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      (∀ k, pDetect k ∈ Set.Icc 0 P) → (∀ k, aDetect k ∈ Set.Icc 0 P) →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : K =>
        slicedDetectionGainLog (degree s) (Cdetect s) count (pDetect s) (pDetect s) (aDetect s)
      let Pk := fun s : K =>
        scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
      let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : K => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
      let Ptail := fun s : K => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget := by
  let Index := Fin (m + 1) × Fin (Cmax + 1)
  let Cs := fun i : Index => Classical.choose
    (exists_primitiveCanonicalSliceEarlyScale_budget m i.1.val i.2.val)
  obtain ⟨A, _, hRadius⟩ := exists_allocatedCommonProductRadiusLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := X + (2 * X + Polynomial.C A) ^ A +
    ∑ s : Index, (X + Polynomial.C (Cs s)) ^ (Cs s)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro K _ degree Cdetect G _ count nX P Bstruct pnum Qstride pDetect aDetect target
    _hStages hdegree hCdetect hP hB hnum hp ha hQ htarget hcount hnX hG
    pRadius D gainLog Pk Tmod E Prho Ptail budget
  let piece := fun s : Index => (P + Cs s) ^ Cs s
  have hpiece (s) : 0 ≤ piece s := by dsimp only [piece]; positivity
  have hradiusBound : 0 ≤ (2 * P + A) ^ A := by positivity
  have hsum0 : 0 ≤ ∑ s, piece s := Finset.sum_nonneg (fun s _ => hpiece s)
  have htotal : P + (2 * P + A) ^ A + ∑ s, piece s ≤ budget := by
    simpa [poly, X, piece, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum] using hbound P hP
  have hbase : P ≤ budget := by linarith only [htotal, hradiusBound, hsum0]
  have hradiusCap : (2 * P + A) ^ A ≤ budget := by linarith only [htotal, hP, hsum0]
  have hpieceCap (s) : piece s ≤ budget := by
    have hi : piece s ≤ ∑ i, piece i :=
      Finset.single_le_sum (fun i _ => hpiece i) (Finset.mem_univ s)
    linarith only [htotal, hi, hP, hradiusBound]
  have hradius : pRadius ∈ Set.Icc 0 budget := by
    refine ⟨(allocatedCommonProductRadius_bounds m hB.1 hB.1).1, ?_⟩
    apply (hRadius hB.1 hB.1).trans
    apply le_trans _ hradiusCap
    exact pow_le_pow_left₀ (by linarith only [hB.1, (show (0 : ℝ) ≤ A from Nat.cast_nonneg A)]) (by linarith only [hB.2]) A
  let index : K → Index := fun s =>
    (⟨degree s, Nat.lt_succ_of_le (hdegree s)⟩,
      ⟨Cdetect s, Nat.lt_succ_of_le (hCdetect s)⟩)
  have hdata (s : K) :
      D ∈ Set.Icc 0 budget ∧ gainLog s ∈ Set.Icc 0 budget ∧
      Pk s ∈ Set.Icc 0 budget ∧ Prho s ∈ Set.Icc 0 budget ∧
      Ptail s ∈ Set.Icc 0 budget ∧ Tmod s ∈ Set.Icc 0 budget := by
    obtain ⟨_, hD, hg, hk, hρ, ht, hmod, _, _⟩ :=
      (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget
        m (degree s) (Cdetect s))).2
        (G := G) hP hnum (hp s) (hp s) (ha s) (htarget s) hQ
        (show (0 : ℝ) ∈ Set.Icc 0 P from ⟨le_rfl, hP⟩) hcount hnX hG
    have lift {x : ℝ} (hx : x ∈ Set.Icc 0 (piece (index s))) : x ∈ Set.Icc 0 budget :=
      ⟨hx.1, hx.2.trans (hpieceCap (index s))⟩
    exact ⟨lift hD, lift hg, lift hk, lift hρ, lift ht, lift hmod⟩
  have hzero : (0 : ℝ) ∈ Set.Icc 0 P := ⟨le_rfl, hP⟩
  obtain ⟨_, hD, _⟩ :=
    (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget m 0 0)).2
      (G := G) hP hnum hzero hzero hzero hzero hQ hzero hcount hnX hG
  have hDCap : D ∈ Set.Icc 0 budget :=
    ⟨hD.1, hD.2.trans (hpieceCap (⟨0, Nat.succ_pos m⟩, ⟨0, Nat.succ_pos Cmax⟩))⟩
  exact ⟨hbase, hradius, hDCap, fun s => (hdata s).2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreePrecisionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreeEarlyBudget
    (m : ℕ) (Cdetect : Fin (m + 1) → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum pDetect aDetect Qstride : ℝ}
      (target : Fin (m + 1) → ℝ),
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : Fin (m + 1) =>
        slicedDetectionGainLog s.val (Cdetect s) count pDetect pDetect aDetect
      let Pk := fun s : Fin (m + 1) =>
        scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
      let Tmod := fun s : Fin (m + 1) => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : Fin (m + 1) => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : Fin (m + 1) => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2) + 2
      let Ptail := fun s : Fin (m + 1) => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget := by
  let Cs := fun s : Fin (m + 1) =>
    Classical.choose (exists_primitiveCanonicalSliceEarlyScale_budget m s.val (Cdetect s))
  obtain ⟨A, _, hRadius⟩ := exists_allocatedCommonProductRadiusLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := X + (2 * X + Polynomial.C A) ^ A +
    ∑ s : Fin (m + 1), (X + Polynomial.C (Cs s)) ^ (Cs s)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P Bstruct pnum pDetect aDetect Qstride target
    hP hB hnum hp ha hQ htarget hcount hnX hG
    pRadius D gainLog Pk Tmod E Prho Ptail budget
  let piece := fun s : Fin (m + 1) => (P + Cs s) ^ Cs s
  have hpiece (s) : 0 ≤ piece s := by dsimp only [piece]; positivity
  have hradiusBound : 0 ≤ (2 * P + A) ^ A := by positivity
  have hsum0 : 0 ≤ ∑ s, piece s := Finset.sum_nonneg (fun s _ => hpiece s)
  have htotal : P + (2 * P + A) ^ A + ∑ s, piece s ≤ budget := by
    simpa [poly, X, piece, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum] using hbound P hP
  have hbase : P ≤ budget := by linarith only [htotal, hradiusBound, hsum0]
  have hradiusCap : (2 * P + A) ^ A ≤ budget := by linarith only [htotal, hP, hsum0]
  have hpieceCap (s) : piece s ≤ budget := by
    have hi : piece s ≤ ∑ i, piece i :=
      Finset.single_le_sum (fun i _ => hpiece i) (Finset.mem_univ s)
    linarith only [htotal, hi, hP, hradiusBound]
  have hradius : pRadius ∈ Set.Icc 0 budget := by
    refine ⟨(allocatedCommonProductRadius_bounds m hB.1 hB.1).1, ?_⟩
    apply (hRadius hB.1 hB.1).trans
    apply le_trans _ hradiusCap
    exact pow_le_pow_left₀ (by linarith only [hB.1, (show (0 : ℝ) ≤ A from Nat.cast_nonneg A)]) (by linarith only [hB.2]) A
  have hdata (s : Fin (m + 1)) :
      D ∈ Set.Icc 0 budget ∧ gainLog s ∈ Set.Icc 0 budget ∧
      Pk s ∈ Set.Icc 0 budget ∧ Prho s ∈ Set.Icc 0 budget ∧
      Ptail s ∈ Set.Icc 0 budget ∧ Tmod s ∈ Set.Icc 0 budget := by
    obtain ⟨_, hD, hg, hk, hρ, ht, hmod, _, _⟩ :=
      (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget m s.val (Cdetect s))).2
        (G := G) hP hnum hp hp ha (htarget s) hQ
        (show (0 : ℝ) ∈ Set.Icc 0 P from ⟨le_rfl, hP⟩) hcount hnX hG
    have lift {x : ℝ} (hx : x ∈ Set.Icc 0 (piece s)) : x ∈ Set.Icc 0 budget :=
      ⟨hx.1, hx.2.trans (hpieceCap s)⟩
    exact ⟨lift hD, lift hg, lift hk, lift hρ, lift ht, lift hmod⟩
  exact ⟨hbase, hradius, (hdata ⟨0, Nat.succ_pos m⟩).1, fun s => (hdata s).2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreePrecisionBudget
    (m : ℕ) (Cdetect : Fin (m + 1) → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P pDetect aDetect Qstride : ℝ},
      0 ≤ P → pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let gainLog := fun s : Fin (m + 1) =>
        slicedDetectionGainLog s.val (Cdetect s) count pDetect pDetect aDetect
      let Pk := fun s : Fin (m + 1) =>
        scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
      let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ s, Pk s
      let target := fun s : Fin (m + 1) =>
        gainLog s + 40 + coefficientErrorSpatialLog Pphysical
      let budget := (P + C) ^ C
      P ≤ budget ∧ Pphysical ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          target s ∈ Set.Icc 0 budget := by
  obtain ⟨A, _, hEarly⟩ := exists_preparedUniformDegreeEarlyBudget m Cdetect
  let X : Polynomial ℕ := Polynomial.X
  let earlyPoly := (X + Polynomial.C A) ^ A
  let physicalPoly := Polynomial.C (m + 2) + 3 * X + Polynomial.C (m + 1) * earlyPoly
  let precisionPoly := earlyPoly + 40 + coefficientErrorSpatialLog physicalPoly
  obtain ⟨C, hC, hBound⟩ :=
    exists_natPolynomial_eval_budget (earlyPoly + physicalPoly + precisionPoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P pDetect aDetect Qstride hP hp ha hQ hcount hnX hG
    gainLog Pk Pphysical target budget
  let early := (P + A) ^ A
  let physical : ℝ := ((m + 2 : ℕ) : ℝ) + 3 * P + ((m + 1 : ℕ) : ℝ) * early
  let precision := early + 40 + coefficientErrorSpatialLog physical
  have hearly0 : 0 ≤ early := by dsimp only [early]; positivity
  have hphysical0 : 0 ≤ physical := by dsimp only [physical]; positivity
  have hprecision0 : 0 ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysical0
    dsimp only [precision]
    positivity
  have htotal : early + physical + precision ≤ budget := by
    simpa [X, earlyPoly, physicalPoly, precisionPoly, early, physical, precision,
      coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
      Polynomial.eval₂_pow] using hBound P hP
  have hearlyCap : early ≤ budget := by linarith only [htotal, hphysical0, hprecision0]
  have hphysicalCap : physical ≤ budget := by linarith only [htotal, hearly0, hprecision0]
  have hprecisionCap : precision ≤ budget := by linarith only [htotal, hearly0, hphysical0]
  have hzero : (0 : ℝ) ∈ Set.Icc 0 P := ⟨le_rfl, hP⟩
  obtain ⟨hPEarly, _, _, hDegrees⟩ :=
    hEarly (G := G) (fun _ => 0) hP hzero hzero hp ha hQ
      (fun _ => hzero) hcount hnX hG
  have hg (s) : gainLog s ∈ Set.Icc 0 early := (hDegrees s).1
  have hk (s) : Pk s ∈ Set.Icc 0 early := (hDegrees s).2.1
  have hsum0 : 0 ≤ ∑ s, Pk s := Finset.sum_nonneg (fun s _ => (hk s).1)
  have hsum : ∑ s, Pk s ≤ ((m + 1 : ℕ) : ℝ) * early := by
    calc
      _ ≤ ∑ _s : Fin (m + 1), early := Finset.sum_le_sum (fun s _ => (hk s).2)
      _ = _ := by simp
  have hactual0 : 0 ≤ Pphysical := by
    have hstride0 := hQ.1
    dsimp only [Pphysical]
    positivity
  have hactual : Pphysical ≤ physical := by
    dsimp only [Pphysical, physical]
    linarith only [hcount, hnX, hQ.2, hsum]
  have hspatial : coefficientErrorSpatialLog Pphysical ≤ coefficientErrorSpatialLog physical := by
    unfold coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  refine ⟨hPEarly.trans hearlyCap, ⟨hactual0, hactual.trans hphysicalCap⟩, ?_⟩
  intro s
  refine ⟨⟨(hg s).1, (hg s).2.trans hearlyCap⟩,
    ⟨(hk s).1, (hk s).2.trans hearlyCap⟩, ?_⟩
  constructor
  · have := (hg s).1
    have := coefficientErrorSpatialLog_nonneg hactual0
    dsimp only [target]
    positivity
  · apply le_trans _ hprecisionCap
    dsimp only [target, precision]
    linarith only [(hg s).2, hspatial]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

structure PreparedUniformDegreeComparison
    {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (s : ℕ) (D target Pk Prho Ptail pDetect : ℝ) where
  ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0
  hρ : ∀ partition, 0 < ρ partition
  hρ1 : ∀ partition, ρ partition ≤ 1
  hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho
  t : ℝ
  ht : 0 < t
  htone : t ≤ 1
  htinv : t⁻¹ ≤ Real.exp Ptail
  hs : AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} (G := G) B
    (fun j : Fin m => (Subtype.val :
      boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
    (Real.exp (-(pDetect + 1)))
    (Real.exp (-(target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5))) ρ t htone

def PreparedUniformDegreeGeometryAt
    {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (s Cdetect nX : ℕ)
    (Bstruct Pscale D target Pk Prho Qstride pDetect pRadius aDetect gainLog : ℝ) : Prop :=
    Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
      (basis := basis) (S := S) (s := s) (nX := nX)
      Bstruct Pscale D target Pk Prho Qstride pDetect
      (Real.toNNReal (Real.exp pRadius))) ∧
    ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
      let gain := (Real.exp (-((5 * pDetect + 20) *
          Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
        Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))
      Real.exp (-gainLog) ≤ gain ∧
        (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊ (gain / 2) : ℝ) ≤
          Real.exp Pk ∧
        scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊ (gain / 2) ≤ S.value

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (α τ : ℝ)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

structure PreparedUniformDegreeDirectScalarBounds
    (m s nX nVars : ℕ) (Cdetect : ℕ)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius u pModel pSlice : ℝ) : Prop where
  master_nonneg : 0 ≤ Pmaster
  late : Pmaster ≤ Plate
  chart_master : Pchart ≤ Pmaster
  dimension_master : D ≤ Pmaster
  radius_master : pRadius ≤ Pmaster
  scale_late : Pscale ≤ Plate
  kernel_scale : Pk ≤ Pscale
  kernel_master : Pk ∈ Set.Icc 0 Pmaster
  stride_master : Qstride ∈ Set.Icc 0 Pmaster
  detect_master : allocatedModelTestLog u pModel ∈ Set.Icc 0 Pmaster
  ambient_master : (nX : ℝ) ≤ Pmaster
  u_master : u ∈ Set.Icc 0 Pmaster
  model_master : pModel ∈ Set.Icc 0 Pmaster
  slice_model : pSlice ≤ pModel
  count_model : (nVars : ℝ) ≤ Real.exp pModel
  rho_master : Prho ∈ Set.Icc 0 Pmaster
  target_master : target ∈ Set.Icc 0 Pmaster
  gain_master : pGain ∈ Set.Icc 0 Pmaster
  coarse_master : pGain + 32 ≤ Pmaster
  coarse_lower : pGain + 32 ≤ coarseTarget
  coarse_late : coarseTarget ≤ Plate
  physical_master : Pphysical ∈ Set.Icc 0 Pmaster
  degree_physical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical
  detector_physical : ((s + 2 : ℕ) : ℝ) ≤ Pphysical
  variables_physical : (nVars : ℝ) ≤ Pphysical
  ambient_physical : (nX : ℝ) ≤ Pphysical
  kernel_physical : Pk ≤ Pphysical
  stride_physical : Qstride ≤ Pphysical
  gain_log : slicedDetectionGainLog s Cdetect nVars
    (allocatedModelTestLog u pModel) (allocatedModelTestLog u pModel)
    (2 * u + 4 * pModel + 7) ≤ pGain
  precision : pGain + 32 + coefficientErrorSpatialLog Pphysical + 8 ≤ target
  xi_late : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
    spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4 ≤ Plate

end Consumer
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedUniformDegreeDirectLate
    (Pmaster Pscale Pphysical coarseTarget extraLate : ℝ) : ℝ :=
  max Pmaster (max Pscale (max coarseTarget (max
    (2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4)
    extraLate)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical BigOperators NNReal

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (selection : Fin (s + 1) ↪ G) (Pdetect : Polynomial ℕ)
variable {Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical
  coarseTarget pRadius u pModel pSlice α : ℝ}

local notation "pDetect" => allocatedModelTestLog u pModel

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

def PreparedFiniteScheduleGeometryPrescribedScaleStatement (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum Qstride : ℝ} (nX : ℕ)
    (pDetect aDetect target : K → ℝ)
 : Prop :=
    let Aradius := Classical.choose (exists_preparedUniformEarlyRadius.{0,0,0,0} m)
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let gainLog := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables G I n B)) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K =>
      scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    pRadius ∈ Set.Icc 0 ((Bstruct + Bstruct + Aradius) ^ Aradius) ∧
    (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧ 0 ≤ D ∧
    (∀ s, 0 ≤ gainLog s ∧ 0 ≤ Pk s ∧ 0 ≤ Prho s ∧ 0 ≤ Ptail s) ∧
    ∃ t : K → ℝ,
      (∀ s, 0 < t s ∧ t s ≤ 1 ∧ (t s)⁻¹ ≤ Real.exp (Ptail s)) ∧
    ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := preparedUniformDegreeTolerance t Qσ
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect s + 2) (Tmod s)
      0 < σ ∧ σ ≤ 1 ∧ (∀ s, σ ≤ t s) ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ 0 ≤ Pscale ∧ D ≤ Pscale ∧
      (∀ s, Pk s ≤ Pscale) ∧
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
      ∀ (S : LayerSamplerScale (G := G) B U basis R (fun _ => σ)),
        (∀ s : K, Real.exp (lengthLogs s) ≤ S.value) →
        ∀ s : K, PreparedUniformDegreeGeometryAt B U basis S (degree s) (Cdetect s) nX
          Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (gainLog s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleDirectMaster {K : Type*} [Fintype K]
    (Pchart D pRadius Qstride Pphysical : ℝ)
    (u pModel Prho target gainLog : K → ℝ) : ℝ :=
  Pchart + D + pRadius + Qstride + Pphysical +
    ∑ k, (u k + pModel k + allocatedModelTestLog (u k) (pModel k) +
      Prho k + target k + gainLog k + 32)

noncomputable def preparedFiniteScheduleDirectCoarse {K : Type*} [Fintype K]
    (gainLog : K → ℝ) (requestedCoarse : ℝ) : ℝ :=
  max (∑ k, (gainLog k + 32)) requestedCoarse

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

abbrev PreparedFiniteForwardSlot (depth : ℕ) := Fin (depth + 1) × Bool

def preparedFiniteForwardSlotDegree {depth : ℕ} (k : PreparedFiniteForwardSlot depth) : ℕ :=
  if k.2 then k.1.val else 0

def preparedFiniteForwardModelSlot {depth : ℕ} (n : Fin (depth + 1)) :
    PreparedFiniteForwardSlot depth := (n, false)

def preparedFiniteForwardDetectionSlot {depth : ℕ} (n : Fin (depth + 1)) :
    PreparedFiniteForwardSlot depth := (n, true)

@[simp] theorem preparedFiniteForwardModelSlot_degree {depth : ℕ} (n : Fin (depth + 1)) :
    preparedFiniteForwardSlotDegree (preparedFiniteForwardModelSlot n) = 0 := rfl

@[simp] theorem preparedFiniteForwardDetectionSlot_degree {depth : ℕ} (n : Fin (depth + 1)) :
    preparedFiniteForwardSlotDegree (preparedFiniteForwardDetectionSlot n) = n.val := rfl

@[simp] theorem preparedFiniteForwardSlot_card (depth : ℕ) :
    Fintype.card (PreparedFiniteForwardSlot depth) = 2 * (depth + 1) := by
  simp [PreparedFiniteForwardSlot, Nat.mul_comm]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleLocalPhysical
    (m nX count : ℕ) (Qstride Pk : ℝ) : ℝ :=
  ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + Pk

noncomputable def preparedFiniteScheduleLocalMaster
    (Pchart D pRadius Qstride Pphysical u pModel Prho target gainLog : ℝ) : ℝ :=
  Pchart + D + pRadius + Qstride + Pphysical +
    (u + pModel + allocatedModelTestLog u pModel + Prho + target + gainLog + 32)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalProductiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

def PreparedFiniteScheduleGeometryStatement (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum Qstride : ℝ} (nX : ℕ)
    (pDetect aDetect target : K → ℝ)
 : Prop :=
    let Aradius := Classical.choose (exists_preparedUniformEarlyRadius.{0,0,0,0} m)
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let gainLog := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables G I n B)) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K =>
      scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    pRadius ∈ Set.Icc 0 ((Bstruct + Bstruct + Aradius) ^ Aradius) ∧
    (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧ 0 ≤ D ∧
    (∀ s, 0 ≤ gainLog s ∧ 0 ≤ Pk s ∧ 0 ≤ Prho s ∧ 0 ≤ Ptail s) ∧
    ∃ t : K → ℝ,
      (∀ s, 0 < t s ∧ t s ≤ 1 ∧ (t s)⁻¹ ≤ Real.exp (Ptail s)) ∧
    ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := preparedUniformDegreeTolerance t Qσ
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect s + 2) (Tmod s)
      0 < σ ∧ σ ≤ 1 ∧ (∀ s, σ ≤ t s) ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ 0 ≤ Pscale ∧ D ≤ Pscale ∧
      (∀ s, Pk s ≤ Pscale) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
        Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
        (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
          8 * (probabilityProfileLipschitz : ℝ) * W ≤
            (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
              ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
        ∀ s : K, PreparedUniformDegreeGeometryAt B U basis S (degree s) (Cdetect s) nX
          Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (gainLog s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BundleCountingRecurrence
namespace OAI

section

namespace Erdos3.FixedDensity

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure HypergraphBundle
    (J K : Type*) [DecidableEq J] [DecidableEq K]
    (H : Finset (Finset J)) where
  edges : Finset (Finset K)
  projection : K → J
  projection_injective_on_edge :
    ∀ g ∈ edges, Set.InjOn projection (g : Set K)
  projection_mem_base :
    ∀ g ∈ edges, g.image projection ∈ H

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def IsClosedUnderInclusion
    (B : HypergraphBundle J K H) : Prop :=
  ∀ ⦃g⦄, g ∈ B.edges →
    ∀ ⦃f⦄, f ⊆ g → f ∈ B.edges

def order (B : HypergraphBundle J K H) : ℕ :=
  B.edges.sup Finset.card

def eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H where
  edges := B.edges.erase g₀
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg)
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl

def edgeTuple
    (g : Finset K) (x : K → G) :
    ({v : K // v ∈ g} → G) :=
  fun v => x v.1

noncomputable def projectionEquiv
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    {v : K // v ∈ g} ≃
      {j : J // j ∈ g.image B.projection} := by
  classical
  apply Equiv.ofBijective
    (fun v : {v : K // v ∈ g} =>
      (⟨B.projection v.1,
        Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}))
  constructor
  · intro v w hvw
    apply Subtype.ext
    apply B.projection_injective_on_edge g hg v.2 w.2
    exact congrArg Subtype.val hvw
  · intro j
    obtain ⟨v, hv, hvj⟩ :=
      Finset.mem_image.mp j.2
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    exact hvj

noncomputable def projectedEdgeTuple
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    ({j : J // j ∈ g.image B.projection} → G) :=
  fun j => y ((B.projectionEquiv hg).symm j)

abbrev BaseEdgeWeight
    (J G : Type*) :=
  (e : Finset J) → ({j : J // j ∈ e} → G) → ℝ

def BaseWeightsInUnitInterval
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, 0 ≤ A e y ∧ A e y ≤ 1

noncomputable def pullbackBaseEdgeWeight
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G) :
    (g : Finset K) → ({v : K // v ∈ g} → G) → ℝ := by
  classical
  intro g y
  by_cases hg : g ∈ B.edges
  · exact A (g.image B.projection)
      (B.projectedEdgeTuple hg y)
  · exact 1

@[simp]
theorem pullbackBaseEdgeWeight_of_mem
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      A (g.image B.projection)
        (B.projectedEdgeTuple hg y) := by
  classical
  simp [pullbackBaseEdgeWeight, hg]

def WeightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y, 0 ≤ A g y ∧ A g y ≤ 1

noncomputable def bundleProduct
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  ∏ g ∈ B.edges, A g (edgeTuple g x)

noncomputable def bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (B.bundleProduct A)

theorem WeightsInUnitInterval.eraseEdge
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (g₀ : Finset K) :
    (B.eraseEdge g₀).WeightsInUnitInterval A := by
  intro g hg y
  exact hA g (Finset.mem_of_mem_erase hg) y

noncomputable def edgeRemainder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  (B.eraseEdge g₀).bundleProduct A x

noncomputable def edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun x : K → G =>
    q (edgeTuple g₀ x) * B.edgeRemainder g₀ A x)

abbrev EdgeComplement (g : Finset K) :=
  {v : K // v ∉ g}

noncomputable def edgeSumEquiv (g : Finset K) :
    {v : K // v ∈ g} ⊕ EdgeComplement g ≃ K :=
  Equiv.sumCompl fun v : K => v ∈ g

noncomputable def splitEdgeEquiv
    (g : Finset K) :
    (K → G) ≃
      (({v : K // v ∈ g} → G) ×
        (EdgeComplement g → G)) :=
  (Equiv.piCongrLeft (fun _ : K => G)
      (edgeSumEquiv g)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : {v : K // v ∈ g} ⊕
        EdgeComplement g => G))

@[simp]
theorem splitEdgeEquiv_fst
    (g : Finset K) (x : K → G) :
    (splitEdgeEquiv g x).1 = edgeTuple g x := by
  funext v
  simp [splitEdgeEquiv, edgeSumEquiv, edgeTuple]

@[simp]
theorem edgeTuple_splitEdgeEquiv_symm
    (g : Finset K)
    (y : {v : K // v ∈ g} → G)
    (z : EdgeComplement g → G) :
    edgeTuple g ((splitEdgeEquiv g).symm (y, z)) = y := by
  rw [← splitEdgeEquiv_fst]
  simp

noncomputable def edgeRemainderFiber
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G) : ℝ :=
  B.edgeRemainder g₀ A
    ((splitEdgeEquiv g₀).symm (y, z))

noncomputable def edgeRemainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  mean (B.edgeRemainderFiber g₀ A y)

noncomputable def frozenEdgeCorrelation
    [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (z : EdgeComplement g₀ → G) : ℝ :=
  mean (fun y =>
    q y * B.edgeRemainderFiber g₀ A y z)

noncomputable def doubledRemainderMoment
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun y =>
    B.edgeRemainderAverage g₀ A y ^ 2)

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleFiltration
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

abbrev DoubledOccurrenceVertex (g₀ : Finset K) :=
  {v : K // v ∈ g₀} ⊕ (Bool × EdgeComplement g₀)

def doubledVertexForget
    (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → K
  | Sum.inl v => v.1
  | Sum.inr v => v.2.1

def doubledVertexLift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    DoubledOccurrenceVertex g₀ :=
  if hv : v ∈ g₀ then
    Sum.inl ⟨v, hv⟩
  else
    Sum.inr ⟨copy, ⟨v, hv⟩⟩

@[simp]
theorem doubledVertexForget_lift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    doubledVertexForget g₀
        (doubledVertexLift g₀ copy v) = v := by
  by_cases hv : v ∈ g₀ <;>
    simp [doubledVertexLift, doubledVertexForget, hv]

theorem doubledVertexLift_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledVertexLift g₀ copy) := by
  intro v w hvw
  have h :=
    congrArg (doubledVertexForget g₀) hvw
  simpa using h

def doubledAssignment
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    DoubledOccurrenceVertex g₀ → G
  | Sum.inl v => y v
  | Sum.inr (false, v) => z.1 v
  | Sum.inr (true, v) => z.2 v

def splitDoubledAssignmentEquiv
    (g₀ : Finset K) :
    (DoubledOccurrenceVertex g₀ → G) ≃
      (({v : K // v ∈ g₀} → G) ×
        ((EdgeComplement g₀ → G) ×
          (EdgeComplement g₀ → G))) where
  toFun x :=
    (fun v => x (Sum.inl v),
      (fun v => x (Sum.inr (false, v)),
        fun v => x (Sum.inr (true, v))))
  invFun p := doubledAssignment g₀ p.1 p.2
  left_inv x := by
    funext v
    rcases v with v | ⟨copy, v⟩
    · rfl
    · cases copy <;> rfl
  right_inv p := by
    rcases p with ⟨y, zfalse, ztrue⟩
    rfl

omit [DecidableEq K] in
@[simp]
theorem splitDoubledAssignmentEquiv_symm_apply
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    (splitDoubledAssignmentEquiv g₀).symm (y, z) =
      doubledAssignment g₀ y z :=
  rfl

@[simp]
theorem doubledAssignment_lift_false
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ false v) =
      (splitEdgeEquiv g₀).symm (y, z.1) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dif_pos hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dif_neg hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

@[simp]
theorem doubledAssignment_lift_true
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ true v) =
      (splitEdgeEquiv g₀).symm (y, z.2) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dif_pos hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dif_neg hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

def doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    Finset (DoubledOccurrenceVertex g₀) :=
  g.image (doubledVertexLift g₀ copy)

theorem mem_doubledEdge
    (g₀ : Finset K) (copy : Bool)
    (g : Finset K) (v : K) (hv : v ∈ g) :
    doubledVertexLift g₀ copy v ∈
      doubledEdge g₀ copy g :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

@[simp]
theorem image_forget_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (doubledVertexForget g₀) = g := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    have huv : u = v := by
      simpa using hwv
    exact huv ▸ hu
  · intro hv
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv, by simp⟩

@[simp]
theorem card_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).card = g.card := by
  rw [doubledEdge,
    Finset.card_image_of_injective _
      (doubledVertexLift_injective g₀ copy)]

abbrev DoubledEdgeSource
    (B : HypergraphBundle J K H) (g₀ : Finset K) :=
  Bool × {g : Finset K // g ∈ (B.edges.erase g₀)}

def doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (s : B.DoubledEdgeSource g₀) :
    Finset (DoubledOccurrenceVertex g₀) :=
  doubledEdge g₀ s.1 s.2.1

noncomputable def doubledSourceProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : DoubledOccurrenceVertex g₀ → G) : ℝ :=
  ∏ s : B.DoubledEdgeSource g₀,
    A s.2.1 (fun v =>
      x (doubledVertexLift g₀ s.1 v.1))

def doubledEdges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    Finset (Finset (DoubledOccurrenceVertex g₀)) :=
  Finset.univ.image (B.doubledEdgeOfSource g₀)

theorem mem_doubledEdges_iff
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (d : Finset (DoubledOccurrenceVertex g₀)) :
    d ∈ B.doubledEdges g₀ ↔
      ∃ (copy : Bool) (g : Finset K),
        g ∈ B.edges.erase g₀ ∧
          doubledEdge g₀ copy g = d := by
  classical
  constructor
  · intro hd
    obtain ⟨s, _hs, hsd⟩ :=
      Finset.mem_image.mp hd
    exact ⟨s.1, s.2.1, s.2.2, hsd⟩
  · rintro ⟨copy, g, hg, rfl⟩
    exact
      Finset.mem_image.mpr
        ⟨(copy, ⟨g, hg⟩), Finset.mem_univ _, rfl⟩

def doubledProjection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → J :=
  fun v => B.projection (doubledVertexForget g₀ v)

@[simp]
theorem doubledProjection_lift
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (v : K) :
    B.doubledProjection g₀
        (doubledVertexLift g₀ copy v) =
      B.projection v := by
  simp [doubledProjection]

@[simp]
theorem image_doubledProjection_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (B.doubledProjection g₀) =
      g.image B.projection := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨w, hw, by simpa using hvj⟩
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv,
          by simpa using hvj⟩

def duplicateOutside
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J (DoubledOccurrenceVertex g₀) H where
  edges := B.doubledEdges g₀
  projection := B.doubledProjection g₀
  projection_injective_on_edge := by
    intro d hd v hv w hw hvw
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    obtain ⟨v₀, hv₀, rfl⟩ :=
      Finset.mem_image.mp hv
    obtain ⟨w₀, hw₀, rfl⟩ :=
      Finset.mem_image.mp hw
    apply congrArg (doubledVertexLift g₀ copy)
    apply B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg) hv₀ hw₀
    simpa using hvw
  projection_mem_base := by
    intro d hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    rw [image_doubledProjection_doubledEdge]
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl

@[simp]
theorem duplicateOutside_projection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).projection =
      B.doubledProjection g₀ :=
  rfl

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    HypergraphBundle J K H where
  edges := B.edges.filter P
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_filter.mp hg).1
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_filter.mp hg).1

@[simp]
theorem filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges = B.edges.filter P :=
  rfl

@[simp]
theorem mem_filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (g : Finset K) :
    g ∈ (B.filterEdges P).edges ↔
      g ∈ B.edges ∧ P g := by
  simp [filterEdges]

@[simp]
theorem filterEdges_projection
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).projection = B.projection :=
  rfl

def lowerOrder
    (B : HypergraphBundle J K H) (d : ℕ) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g.card < d

@[simp]
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl

@[simp]
theorem mem_lowerOrder_edges
    (B : HypergraphBundle J K H)
    (d : ℕ) (g : Finset K) :
    g ∈ (B.lowerOrder d).edges ↔
      g ∈ B.edges ∧ g.card < d := by
  simp [lowerOrder]

def strictBoundary
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g ⊂ g₀

@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl

@[simp]
theorem mem_strictBoundary_edges
    (B : HypergraphBundle J K H)
    (g₀ g : Finset K) :
    g ∈ (B.strictBoundary g₀).edges ↔
      g ∈ B.edges ∧ g ⊂ g₀ := by
  simp [strictBoundary]

noncomputable def bundleMainProduct
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges, p (g.image B.projection)

@[simp]
theorem bundleMainProduct_filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (p : Finset J → ℝ) :
    (B.filterEdges P).bundleMainProduct p =
      ∏ g ∈ B.edges.filter P,
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_lowerOrder
    (B : HypergraphBundle J K H)
    (d : ℕ) (p : Finset J → ℝ) :
    (B.lowerOrder d).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g.card < d),
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_strictBoundary
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g ⊂ g₀),
        p (g.image B.projection) :=
  rfl

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleEnvelopeSelection
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def BaseWeightsIdempotent
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, A e y * A e y = A e y

def finsetMembershipEquivOfEq
    {α : Type*} {s t : Finset α} (h : s = t) :
    {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
  Equiv.cast
    (congrArg (fun u : Finset α => {a : α // a ∈ u}) h)

@[simp]
theorem finsetMembershipEquivOfEq_symm_val
    {α : Type*} {s t : Finset α} (h : s = t)
    (a : {a : α // a ∈ t}) :
    ((finsetMembershipEquivOfEq h).symm a).1 = a.1 := by
  subst t
  rfl

@[simp]
theorem projectionEquiv_apply_val
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (v : {v : K // v ∈ g}) :
    ((B.projectionEquiv hg) v).1 =
      B.projection v.1 := by
  rfl

noncomputable def doubledBundleEdgeFactor
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀)) : ℝ :=
  (B.duplicateOutside g₀).pullbackBaseEdgeWeight A d
    (edgeTuple d x)

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def restrictEdgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (y : {v : K // v ∈ g} → G) :
    {v : K // v ∈ f} → G :=
  fun v => y ⟨v.1, hfg v.2⟩

omit [DecidableEq K] in
@[simp]
theorem restrictEdgeTuple_edgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (x : K → G) :
    restrictEdgeTuple hfg (edgeTuple g x) =
      edgeTuple f x := by
  rfl

noncomputable def strictBoundaryLocalProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  ∏ g :
      {g : Finset K //
        g ∈ (B.strictBoundary g₀).edges},
    A g.1
      (restrictEdgeTuple
        (((B.mem_strictBoundary_edges g₀ g.1).1
          g.2).2.1)
        y)

def WeightsIdempotent
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y,
    A g y * A g y = A g y

noncomputable def lowerExteriorMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges.filter
      (fun g =>
        g.card < g₀.card ∧ ¬ g ⊆ g₀),
    p (g.image B.projection)

noncomputable def maximalRemainderMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card),
    p (g.image B.projection)

end HypergraphBundle

structure IsBundleCountingEnvelope
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ) : Prop where
  density_pos : ∀ d, 0 < α d
  density_le_one : ∀ d, α d ≤ 1
  defect_nonneg : ∀ d, 0 ≤ β d
  uniform_nonneg : 0 ≤ τ
  floor_pos : ∀ d, 0 < μ d
  rankFloor :
    ∀ ⦃i d : ℕ⦄, i ≤ d → μ d ≤ α i
  error_nonneg :
    ∀ d n, 0 ≤ E d n
  error_mono_order :
    ∀ ⦃d d' n : ℕ⦄, d ≤ d' →
      E d n ≤ E d' n
  error_mono_card :
    ∀ ⦃d n n' : ℕ⦄, n ≤ n' →
      E d n ≤ E d n'
  step :
    ∀ d n,
      E (d + 1) n +
            Real.sqrt
                (β (d + 1) *
                  (1 + E d (n + 1)) *
                  (1 + E d (2 * (n + 1)))) /
              (α (d + 1)) ^ (n + 1) +
          τ / (μ (d + 1)) ^ (n + 1) ≤
        E (d + 1) (n + 1)

noncomputable def bundleCountingStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + E d (n + 1)) *
          (1 + E d (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open Filter Topology

noncomputable def bundleCommonStepIncrement
    (a t : ℝ) (lower : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt
        (t ^ 2 *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      a ^ (n + 1) +
    t ^ 2 / a ^ (n + 1)

noncomputable def bundleCommonNextRow
    (a t : ℝ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      bundleCommonNextRow a t lower n +
        bundleCommonStepIncrement a t lower n

noncomputable def bundleCommonEnvelopeError
    (a t : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      bundleCommonNextRow a t
        (bundleCommonEnvelopeError a t d)

@[simp]
theorem bundleCommonNextRow_zero
    (a t : ℝ) (lower : ℕ → ℝ) :
    bundleCommonNextRow a t lower 0 = 0 :=
  rfl

@[simp]
theorem bundleCommonNextRow_succ
    (a t : ℝ) (lower : ℕ → ℝ) (n : ℕ) :
    bundleCommonNextRow a t lower (n + 1) =
      bundleCommonNextRow a t lower n +
        bundleCommonStepIncrement a t lower n :=
  rfl

@[simp]
theorem bundleCommonEnvelopeError_zero_order
    (a t : ℝ) (n : ℕ) :
    bundleCommonEnvelopeError a t 0 n = 0 :=
  rfl

@[simp]
theorem bundleCommonEnvelopeError_succ_order
    (a t : ℝ) (d n : ℕ) :
    bundleCommonEnvelopeError a t (d + 1) n =
      bundleCommonNextRow a t
        (bundleCommonEnvelopeError a t d) n :=
  rfl

@[simp]
theorem bundleCommonNextRow_zero_parameter
    (a : ℝ) (lower : ℕ → ℝ)
    (hlower : ∀ n, lower n = 0) :
    ∀ n, bundleCommonNextRow a 0 lower n = 0 := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      rw [bundleCommonNextRow_succ, ihn]
      simp [bundleCommonStepIncrement, hlower]

@[simp]
theorem bundleCommonEnvelopeError_zero_parameter
    (a : ℝ) :
    ∀ d n, bundleCommonEnvelopeError a 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ihd =>
      intro n
      rw [bundleCommonEnvelopeError_succ_order]
      exact bundleCommonNextRow_zero_parameter a
        (bundleCommonEnvelopeError a 0 d) ihd n

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleRelativeCounting
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

end HypergraphBundle

universe uJ uG

variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}

def HasTaoBundleCountingStep
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (β : ℕ → ℝ) (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, g₀ ∈ B.edges →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      |B.bundleCount (B.pullbackBaseEdgeWeight A) -
          p (g₀.image B.projection) *
            (B.eraseEdge g₀).bundleCount
              ((B.eraseEdge g₀).pullbackBaseEdgeWeight A)| ≤
        Real.sqrt
            (β g₀.card *
              (B.strictBoundary g₀).bundleCount
                ((B.strictBoundary g₀).pullbackBaseEdgeWeight A) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                  A)) +
          τ

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleFrozenUniformity
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    Finset (Fin k) :=
  Finset.univ.map e.face.toEmbedding

@[simp]
theorem positiveOrderedFaceEdge_card
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card = e.rank := by
  simp [positiveOrderedFaceEdge, PositiveOrderedFace.rank]

theorem positiveOrderedFaceEdge_nonempty
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).Nonempty := by
  apply Finset.card_pos.mp
  rw [positiveOrderedFaceEdge_card]
  exact e.rank_pos

theorem positiveOrderedFaceEdge_card_le
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card ≤ r := by
  rw [positiveOrderedFaceEdge_card]
  unfold PositiveOrderedFace.rank
  omega

@[simp]
theorem mem_positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (v : Fin k) :
    v ∈ positiveOrderedFaceEdge e ↔
      v ∈ Set.range e.face := by
  simp [positiveOrderedFaceEdge]

noncomputable def positiveOrderedFaceOfEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨t.card - 1, by
      have htcard : 0 < t.card :=
        Finset.card_pos.mpr ht
      omega⟩
  refine ⟨j, ?_⟩
  have hcard : t.card = j.1 + 1 := by
    dsimp [j]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact t.orderEmbOfFin hcard

@[simp]
theorem positiveOrderedFaceEdge_ofEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    positiveOrderedFaceEdge
        (positiveOrderedFaceOfEdge t ht htr) = t := by
  dsimp only [positiveOrderedFaceEdge, positiveOrderedFaceOfEdge]
  exact Finset.map_orderEmbOfFin_univ t _

theorem positiveOrderedFaceEdge_injective
    {k r : ℕ} :
    Function.Injective
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)) := by
  intro e f hef
  have hrank : e.rank = f.rank := by
    rw [← positiveOrderedFaceEdge_card e,
      ← positiveOrderedFaceEdge_card f, hef]
  rcases e with ⟨je, e⟩
  rcases f with ⟨jf, f⟩
  simp only [PositiveOrderedFace.rank] at hrank
  have hj : je = jf := by
    apply Fin.ext
    omega
  subst jf
  have hrange : Set.range e = Set.range f := by
    ext v
    have hv :=
      congrArg
        (fun s : Finset (Fin k) => v ∈ s) hef
    simpa [positiveOrderedFaceEdge] using hv
  have hef' : e = f :=
    (OrderEmbedding.range_inj).mp hrange
  subst f
  rfl

@[simp]
theorem positiveOrderedFaceOfEdge_edge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    positiveOrderedFaceOfEdge
        (positiveOrderedFaceEdge e)
        (positiveOrderedFaceEdge_nonempty e)
        (positiveOrderedFaceEdge_card_le e) = e := by
  apply positiveOrderedFaceEdge_injective
  exact positiveOrderedFaceEdge_ofEdge
    (positiveOrderedFaceEdge e)
    (positiveOrderedFaceEdge_nonempty e)
    (positiveOrderedFaceEdge_card_le e)

noncomputable def orderedConfigurationBaseEdges
    (k r : ℕ) : Finset (Finset (Fin k)) :=
  insert ∅
    (Finset.univ.image
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)))

@[simp]
theorem empty_mem_orderedConfigurationBaseEdges
    (k r : ℕ) :
    ∅ ∈ orderedConfigurationBaseEdges k r := by
  simp [orderedConfigurationBaseEdges]

@[simp]
theorem mem_orderedConfigurationBaseEdges_iff
    {k r : ℕ} (t : Finset (Fin k)) :
    t ∈ orderedConfigurationBaseEdges k r ↔
      t.card ≤ r := by
  constructor
  · intro ht
    rw [orderedConfigurationBaseEdges,
      Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · simp
    · obtain ⟨e, _he, rfl⟩ :=
        Finset.mem_image.mp ht
      exact positiveOrderedFaceEdge_card_le e
  · intro htr
    by_cases ht0 : t = ∅
    · subst t
      exact empty_mem_orderedConfigurationBaseEdges k r
    · have ht : t.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr ht0
      rw [orderedConfigurationBaseEdges,
        Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      refine
        ⟨positiveOrderedFaceOfEdge t ht htr,
          Finset.mem_univ _, ?_⟩
      exact positiveOrderedFaceEdge_ofEdge t ht htr

noncomputable def orderedConfigurationInitialBundle
    (k r : ℕ) :
    HypergraphBundle (Fin k) (Fin k)
      (orderedConfigurationBaseEdges k r) where
  edges := orderedConfigurationBaseEdges k r
  projection := id
  projection_injective_on_edge := by
    intro g hg x hx y hy hxy
    exact hxy
  projection_mem_base := by
    intro g hg
    simpa using hg

@[simp]
theorem orderedConfigurationInitialBundle_edges
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).edges =
      orderedConfigurationBaseEdges k r :=
  rfl

@[simp]
theorem orderedConfigurationInitialBundle_projection
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).projection =
      id :=
  rfl

noncomputable def orderedConfigurationEdgeTuple
    {G : Type*} {k r : ℕ}
    (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r)
    (y : {v : Fin k // v ∈ t} → G) :
    Fin ((positiveOrderedFaceOfEdge t ht htr).lowerRank.1 + 1) → G := by
  let e := positiveOrderedFaceOfEdge t ht htr
  have hcard : t.card = e.lowerRank.1 + 1 := by
    dsimp [e, positiveOrderedFaceOfEdge]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact fun i => y (t.orderIsoOfFin hcard i)

@[simp]
theorem positiveOrderedFaceEdge_orderIsoOfFin_val
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (i : Fin (e.lowerRank.1 + 1)) :
    ((positiveOrderedFaceEdge e).orderIsoOfFin
        (by
          simp [PositiveOrderedFace.rank]) i).1 =
      e.face i := by
  rw [Finset.coe_orderIsoOfFin_apply]
  have hcanonical :
      e.face =
        (positiveOrderedFaceEdge e).orderEmbOfFin
          (by
            simp [PositiveOrderedFace.rank]) := by
    apply Finset.orderEmbOfFin_unique'
    intro q
    simp [positiveOrderedFaceEdge]
  exact congrArg (fun f => f i) hcanonical.symm

noncomputable def orderedConfigurationBaseWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseEdgeWeight (Fin k) G := by
  classical
  intro t y
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact configurationFaceWeight A
        (positiveOrderedFaceOfEdge t ht htr)
        (orderedConfigurationEdgeTuple t ht htr y)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (y : {v : Fin k // v ∈ (∅ : Finset (Fin k))} → G) :
    orderedConfigurationBaseWeight A ∅ y = 1 := by
  simp [orderedConfigurationBaseWeight]

@[simp]
theorem orderedConfigurationBaseWeight_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y :
      {v : Fin k // v ∈ positiveOrderedFaceEdge e} → G) :
    orderedConfigurationBaseWeight A
        (positiveOrderedFaceEdge e) y =
      configurationFaceWeight A e
        (fun i =>
          y ⟨e.face i,
            (mem_positiveOrderedFaceEdge e
              (e.face i)).2 ⟨i, rfl⟩⟩) := by
  classical
  simp only [orderedConfigurationBaseWeight,
    dif_pos (positiveOrderedFaceEdge_nonempty e),
    dif_pos (positiveOrderedFaceEdge_card_le e)]
  change
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
        ⟨positiveOrderedFaceOfEdge
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e),
          orderedConfigurationEdgeTuple
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e) y⟩ =
      (fun p :
          (Σ f : PositiveOrderedFace k r,
            Fin (f.lowerRank.1 + 1) → G) =>
        configurationFaceWeight A p.1 p.2)
          ⟨e, fun i =>
            y ⟨e.face i,
              (mem_positiveOrderedFaceEdge e
                (e.face i)).2 ⟨i, rfl⟩⟩⟩
  apply congrArg
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
  have he :
      positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e) = e :=
    positiveOrderedFaceOfEdge_edge e
  apply Sigma.ext he
  simp only
  apply Function.hfunext
    (congrArg
      (fun f : PositiveOrderedFace k r =>
        Fin (f.lowerRank.1 + 1)) he)
  intro i i' hii
  apply heq_of_eq
  unfold orderedConfigurationEdgeTuple
  apply congrArg y
  apply Subtype.ext
  have hn :
      (positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e)).lowerRank.1 + 1 =
        e.lowerRank.1 + 1 :=
    congrArg (fun f : PositiveOrderedFace k r =>
      f.lowerRank.1 + 1) he
  have hval : i.1 = i'.1 := by
    have hcast :
        cast (congrArg Fin hn) i = i' := by
      exact eq_of_heq
        ((cast_heq (congrArg Fin hn) i).trans hii)
    calc
      i.1 = (cast (congrArg Fin hn) i).1 := by
        symm
        have hcastVal :
            ∀ {m n : ℕ} (h : m = n) (a : Fin m),
              (cast (congrArg Fin h) a).1 = a.1 := by
          intro m n h a
          cases h
          rfl
        exact hcastVal hn i
      _ = i'.1 := congrArg Fin.val hcast
  rw [Finset.coe_orderIsoOfFin_apply]
  calc
    (positiveOrderedFaceEdge e).orderEmbOfFin _ i =
        (positiveOrderedFaceEdge e).orderEmbOfFin _ i' :=
      Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr hval
    _ = e.face i' := by
      simpa only [Finset.coe_orderIsoOfFin_apply] using
        positiveOrderedFaceEdge_orderIsoOfFin_val e i'

noncomputable def orderedConfigurationBaseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    Finset (Fin k) → ℝ := by
  classical
  intro t
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact mixedConfigurationCoarseDensity P A
        (positiveOrderedFaceOfEdge t ht htr)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    orderedConfigurationBaseDensity P A ∅ = 1 := by
  simp [orderedConfigurationBaseDensity]

@[simp]
theorem orderedConfigurationBaseDensity_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    orderedConfigurationBaseDensity P A
        (positiveOrderedFaceEdge e) =
      mixedConfigurationCoarseDensity P A e := by
  classical
  unfold orderedConfigurationBaseDensity
  simp only [dif_pos (positiveOrderedFaceEdge_nonempty e)]
  have hcard :
      (positiveOrderedFaceEdge e).card ≤ r := by
    simpa [positiveOrderedFaceEdge_card] using
      positiveOrderedFaceEdge_card_le e
  simp only [dif_pos hcard]
  exact congrArg (mixedConfigurationCoarseDensity P A)
    (positiveOrderedFaceOfEdge_edge e)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem projectedEdge_nonempty
    {K : Type*} [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (_hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (g.image B.projection).Nonempty := by
  exact Finset.image_nonempty.mpr hne

theorem projectedEdge_card_le
    {K : Type*} [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card ≤ r := by
  exact
    (mem_orderedConfigurationBaseEdges_iff
      (g.image B.projection)).1
      (B.projection_mem_base g hg)

noncomputable def orderedConfigurationBundleFace
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    PositiveOrderedFace k r :=
  positiveOrderedFaceOfEdge
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)

noncomputable def orderedConfigurationBundleFaceTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G :=
  orderedConfigurationEdgeTuple
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)
    (B.projectedEdgeTuple hg y)

noncomputable def orderedConfigurationBundleDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationDefect P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

noncomputable def orderedConfigurationBundleUniform
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationUniform P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

noncomputable def orderedConfigurationBundleLocalizedDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  B.orderedConfigurationBundleDefect P A hg hne y *
    B.strictBoundaryLocalProduct g
      (B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)) y

def HasOrderedConfigurationBundleLocalizedDefect
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      mean (fun y =>
        B.orderedConfigurationBundleLocalizedDefect
            P A hg₀ hne y ^ 2) ≤
        β g₀.card *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A))

def HasOrderedConfigurationBundleFrozenUniformity
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        |B.frozenEdgeCorrelation g₀
            (B.orderedConfigurationBundleUniform
              P A hg₀ hne)
            (B.pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) z| ≤
          τ

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem exists_selectedVertex_not_mem_of_mem_erase
    {J K : Type*} [DecidableEq J] [DecidableEq K]
    {H : Finset (Finset J)}
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card) :
    ∃ v ∈ g₀, v ∉ g := by
  classical
  by_contra hmissing
  have hsubset : g₀ ⊆ g := by
    intro v hv
    by_contra hvg
    exact hmissing ⟨v, hv, hvg⟩
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le hsubset (hmax g hgB)
  exact (Finset.mem_erase.mp hg).1 heq.symm

noncomputable def orderedConfigurationBundleFaceState
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    FaceRegularityState
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  ⟨orderedBoundaryPartition
    (positiveFaceLowerLayer P.fine
      (B.orderedConfigurationBundleFace hg hne))
    (B.orderedConfigurationBundleFace hg hne).face⟩

noncomputable def orderedConfigurationBundleFaceTarget
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
      G) → ℝ :=
  partitionAtomIndicator
    (P.coarse.partition
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)
    (A.atom
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)

def HasOrderedConfigurationBundleFrozenCutRepresentation
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        ∃ u :
            CutTestFamily G
              ((B.orderedConfigurationBundleFace
                hg₀ hne).lowerRank.1 + 1),
          IsBoundedCutTest u ∧
            B.frozenEdgeCorrelation g₀
                (B.orderedConfigurationBundleUniform
                  P A hg₀ hne)
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) z =
              (B.orderedConfigurationBundleFaceState
                  P hg₀ hne).faceCutCorrelation
                (B.orderedConfigurationBundleFaceTarget
                  P A hg₀ hne)
                u

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleSourceGoodnessBridge
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

noncomputable def projectedEdgeOrderIso
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.orderedConfigurationBundleFace hg hne
  have hcard : t.card = e.lowerRank.1 + 1 := by
    have hedge :
        positiveOrderedFaceEdge e = t := by
      dsimp [e, orderedConfigurationBundleFace, t]
      exact positiveOrderedFaceEdge_ofEdge
        (g.image B.projection)
        (B.projectedEdge_nonempty hg hne)
        (B.projectedEdge_card_le hg)
    calc
      t.card = (positiveOrderedFaceEdge e).card :=
        congrArg Finset.card hedge.symm
      _ = e.rank := positiveOrderedFaceEdge_card e
      _ = e.lowerRank.1 + 1 := rfl
  exact (t.orderIsoOfFin hcard).toEquiv

@[simp]
theorem projectedEdgeOrderIso_apply_val
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (i : Fin ((B.orderedConfigurationBundleFace
      hg hne).lowerRank.1 + 1)) :
    ((B.projectedEdgeOrderIso hg hne) i).1 =
      (B.orderedConfigurationBundleFace hg hne).face i := by
  rfl

noncomputable def orderedConfigurationBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.projectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem orderedConfigurationBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.orderedConfigurationBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold orderedConfigurationBundleFaceTupleEquiv
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple projectedEdgeOrderIso
  rfl

def ambientPositiveFaceOfProperSubface
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    PositiveOrderedFace k r where
  lowerRank :=
    ⟨d.lowerRank.1,
      lt_trans d.lowerRank.2 e.lowerRank.2⟩
  face := orderedFullLowerAmbientFace e d

@[simp]
theorem ambientPositiveFaceOfProperSubface_rank
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    (ambientPositiveFaceOfProperSubface e d).rank = d.rank := by
  rfl

noncomputable def orderedConfigurationStrictFaceFamily
    (e : PositiveOrderedFace k r) :
    Finset (PositiveOrderedFace k r) :=
  Finset.univ.filter fun f =>
    positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e

@[simp]
theorem mem_orderedConfigurationStrictFaceFamily
    (e f : PositiveOrderedFace k r) :
    f ∈ orderedConfigurationStrictFaceFamily e ↔
      positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e := by
  simp [orderedConfigurationStrictFaceFamily]

noncomputable def extendConfigurationFaceTuple
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    Fin k → G :=
  (splitOrderedFaceEquiv e.face).symm
    (y, orderedFaceComplementTuple e.face A.witness)

@[simp]
theorem orderedFaceTuple_extendConfigurationFaceTuple
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFaceTuple e.face
        (extendConfigurationFaceTuple P A e y) = y := by
  exact orderedFaceTuple_splitOrderedFaceEquiv_symm _ _ _

@[simp]
theorem extendConfigurationFaceTuple_projection
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G)
    (v : {v : K // v ∈ g}) :
    extendConfigurationFaceTuple P A
        (B.orderedConfigurationBundleFace hg hne)
        (B.orderedConfigurationBundleFaceTuple hg hne y)
        (B.projection v.1) =
      y v := by
  let j := B.projectionEquiv hg v
  let i :=
    (B.projectedEdgeOrderIso hg hne).symm j
  have hi :
      B.projectedEdgeOrderIso hg hne i = j :=
    (B.projectedEdgeOrderIso hg hne).apply_symm_apply j
  have hface :
      (B.orderedConfigurationBundleFace hg hne).face i =
        B.projection v.1 := by
    calc
      (B.orderedConfigurationBundleFace hg hne).face i =
          ((B.projectedEdgeOrderIso hg hne) i).1 := by
        rw [B.projectedEdgeOrderIso_apply_val]
      _ = j.1 := congrArg Subtype.val hi
      _ = B.projection v.1 := by
        exact B.projectionEquiv_apply_val hg v
  rw [← hface]
  change
    orderedFaceTuple
        (B.orderedConfigurationBundleFace hg hne).face
        (extendConfigurationFaceTuple P A
          (B.orderedConfigurationBundleFace hg hne)
          (B.orderedConfigurationBundleFaceTuple hg hne y)) i =
      y v
  rw [orderedFaceTuple_extendConfigurationFaceTuple]
  change
    B.projectedEdgeTuple hg y
        ((B.projectedEdgeOrderIso hg hne) i) =
      y v
  rw [hi]
  exact congrArg y
    ((B.projectionEquiv hg).symm_apply_apply v)

def liftProjectedSubedge
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    Finset K :=
  g₀.filter fun v => B.projection v ∈ t

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Conclusions
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

noncomputable def frozenProjectedEdgeOrderIso
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.orderedConfigurationBundleFace hg hne
  have hcard : t.card = e.lowerRank.1 + 1 := by
    have hedge :
        positiveOrderedFaceEdge e = t := by
      dsimp [e, orderedConfigurationBundleFace, t]
      exact positiveOrderedFaceEdge_ofEdge
        (g.image B.projection)
        (B.projectedEdge_nonempty hg hne)
        (B.projectedEdge_card_le hg)
    calc
      t.card = (positiveOrderedFaceEdge e).card :=
        congrArg Finset.card hedge.symm
      _ = e.rank := positiveOrderedFaceEdge_card e
      _ = e.lowerRank.1 + 1 := rfl
  exact (t.orderIsoOfFin hcard).toEquiv

noncomputable def frozenOccurrenceOrderEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {v : K // v ∈ g} :=
  (B.frozenProjectedEdgeOrderIso hg hne).trans
    (B.projectionEquiv hg).symm

noncomputable def frozenBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.frozenProjectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.frozenBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold frozenBundleFaceTupleEquiv frozenProjectedEdgeOrderIso
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple
  rfl

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_symm_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G)
    (v : {v : K // v ∈ g}) :
    (B.frozenBundleFaceTupleEquiv hg hne).symm x v =
      x ((B.frozenOccurrenceOrderEquiv hg hne).symm v) := by
  rfl

noncomputable def frozenBundleMissingVertex
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) : {v : K // v ∈ g₀} :=
  if hg : g ∈ B.edges.erase g₀ then
    ⟨Classical.choose
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax),
      (Classical.choose_spec
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).1⟩
  else
    ⟨Classical.choose hne, Classical.choose_spec hne⟩

noncomputable def frozenBundleMissingCoordinate
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) :
    Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
    (B.frozenBundleMissingVertex hmax hne g)

noncomputable def frozenBundleInsertedSelectedTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G) :
    {v : K // v ∈ g₀} → G :=
  (B.frozenBundleFaceTupleEquiv hg₀ hne).symm
    (Fin.insertNth i a y)

noncomputable def frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G)
    (z : EdgeComplement g₀ → G) : K → G :=
  (splitEdgeEquiv g₀).symm
    (B.frozenBundleInsertedSelectedTuple hg₀ hne i a y, z)

noncomputable def frozenBundleRemainderCutTest
    {K : Type*} [Fintype K] [DecidableEq K]
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G) :
    CutTestFamily G
      ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  fun i y =>
    ∏ g ∈ B.edges.erase g₀,
      if _hcoord :
          B.frozenBundleMissingCoordinate hg₀ hmax hne g = i
      then
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a y z))
      else 1

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def sourceBundleRemovalHorizon (k r : ℕ) : ℕ :=
  bundleReverseDoublingHorizon r
    (orderedConfigurationInitialBundle k r).edges.card 0

noncomputable def sourceBundleRemovalDensityBudget
    (ε : ℝ) (r : ℕ) : ℝ :=
  min ε 1 /
    (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ)

noncomputable def sourceBundleRemovalStep (k r : ℕ) : ℝ :=
  1 /
    (4 * (r * sourceBundleRemovalHorizon k r + 1 : ℕ) : ℕ)

noncomputable def sourceBundleRemovalKappa (k r : ℕ) : ℝ :=
  sourceBundleRemovalStep k r / 8

noncomputable def sourceBundleRemovalCountThreshold
    (k r ceiling : ℕ) (δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    sourceBundleDensity δ ceiling ^
      Fintype.card (PositiveOrderedFace k r)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialGroupMapChart
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial _root_.MvPolynomial

variable {σ τ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartHom

theorem realPolynomialGroupMap_weightedAdaptedRealChartHom
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialGroupMap G φ hφ v (F.weightedAdaptedRealChartHom w v β hβ g) =
      G.weightedAdaptedRealChartHom w v β hβ (F.realPolynomialGroupMap G φ hφ w g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [realPolynomialGroupMap_log, weightedAdaptedRealChartHom_coord]
  exact (realChartSubstitute_map β (realificationLieHom φ).toLinearMap _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedCommonRadiusDensityCapNested
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem exists_commonRadius_densityCap_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ p : ℝ, 0 ≤ p → (m : ℝ) ≤ p →
      ∀ a n : Fin m → ℕ, (∀ j, (a j : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      4 * ∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m p p) (V j) ≤ Real.exp ((p + A) ^ A) := by
  let rad : Polynomial ℕ := allocatedCommonProductRadiusLog m Polynomial.X Polynomial.X
  let env : Polynomial ℕ := Polynomial.X + rad + 4
  let cap : Polynomial ℕ := 3 * env ^ 3 + 17 * env ^ 2 + 4
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget cap
  refine ⟨A, hA, ?_⟩
  intro p hp hm a n ha hn V hV hprofile
  let E := p + allocatedCommonProductRadiusLog m p p + 4
  obtain ⟨hrad, hR, _, hRinv, _⟩ := allocatedCommonProductRadius_bounds m hp hp
  have hpE : p ≤ E := by dsimp only [E]; linarith
  have hradE : allocatedCommonProductRadiusLog m p p ≤ E := by dsimp only [E]; linarith
  have hE : 0 ≤ E := hp.trans hpE
  have heval : env.eval₂ (Nat.castRingHom ℝ) p = E := by
    simp [env, rad, E, allocatedCommonProductRadiusLog, allocatedCommonRadiusLog,
      allocatedBufferedRadiusLog, allocatedBufferedRadiusInput, allocatedProductChartLog,
      allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
      allocatedComparisonDimension, Polynomial.eval₂_pow]
  have hcap : earlyFiberCapLog E + 4 ≤ (p + A) ^ A := by
    simpa only [cap, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_ofNat, heval, earlyFiberCapLog] using hbound p hp
  have hprod := earlyFiberCap_exp_bound a n (fun _ => allocatedCommonProductRadius m p p)
    (fun j => (V j : ℝ)) hE (hm.trans hpE) (fun _ => hR)
    (fun j => (V j).coe_nonneg) (fun j => (ha j).trans hpE)
    (fun j => (hn j).trans hpE) (hprofile.trans (Real.exp_le_exp.mpr hpE))
    (fun _ => hRinv.le.trans (Real.exp_le_exp.mpr hradE))
    (fun j => (hV j).trans (Real.exp_le_exp.mpr hpE))
  calc
    4 * ∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m p p) (V j)
      ≤ Real.exp 4 * Real.exp (earlyFiberCapLog E) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (4 : ℝ)]) hprod
          (Finset.prod_nonneg (fun j _ => earlyConstantDensityCap_nonneg _ _ hR (V j).coe_nonneg))
          (Real.exp_nonneg _)
    _ = Real.exp (earlyFiberCapLog E + 4) := by rw [← Real.exp_add, add_comm]
    _ ≤ _ := Real.exp_le_exp.mpr hcap

theorem exists_commonRadius_densityCap_uniform_bound (maxLayers : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      ∀ m : ℕ, m ≤ maxLayers → ∀ p : ℝ, 0 ≤ p → (m : ℝ) ≤ p →
      ∀ a n : Fin m → ℕ, (∀ j, (a j : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      4 * ∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m p p) (V j) ≤ Real.exp ((p + A) ^ A) := by
  classical
  choose ex hex hb using fun j : Fin (maxLayers + 1) => exists_commonRadius_densityCap_bound j.val
  let A₀ := 2 + ∑ j, ex j
  refine ⟨A₀, by dsimp only [A₀]; omega, ?_⟩
  intro A hA m hm p hp hmp a n ha hn V hV hprofile
  let j : Fin (maxLayers + 1) := ⟨m, by omega⟩
  have hsum : ex j ≤ ∑ i, ex i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hEA : ex j ≤ A := by dsimp only [A₀] at hA; omega
  have hAtwo : (2 : ℝ) ≤ A := by exact_mod_cast (hex j).trans hEA
  have hpow : (p + ex j) ^ ex j ≤ (p + A) ^ A :=
    (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hEA)) _).trans
      (pow_le_pow_right₀ (by linarith) hEA)
  exact (hb j p hp hmp a n ha hn V hV hprofile).trans (Real.exp_le_exp.mpr hpow)

theorem exists_prepared_commonRadius_densityCap_forward_bound (maxLayers : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      ∀ {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m),
      m ≤ maxLayers → ∀ M Jalloc : ℕ,
      (∀ j, Fintype.card (prep j).Coord ≤ M) →
      ∀ p : ℝ, 0 ≤ p → (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      ∀ stageCountConstant : ℕ → ℕ, ∀ stage : ℕ,
      4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
        (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j) ≤
          Real.exp (preparedFiniteForwardWork A stageCountConstant stage p) := by
  obtain ⟨A₀, hA₀, hcap⟩ := exists_commonRadius_densityCap_uniform_bound maxLayers
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA X J m prep hm M Jalloc hM p hp hnum V hV hprofile constants stage
  obtain ⟨_, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions prep Jalloc hM
  have hmdim : m ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
    unfold enlargedPreparedCommonSamplerDimension
    omega
  have h := hcap A hA m hm p hp ((Nat.cast_le.mpr hmdim).trans hnum)
    (fun j => Fintype.card (PreparedSamplerContinuous prep j)) (preparedSamplerTransverse prep)
    (fun j => (Nat.cast_le.mpr (hI j)).trans hnum)
    (fun j => (Nat.cast_le.mpr (hn j)).trans hnum) V hV hprofile
  apply h.trans (Real.exp_le_exp.mpr ?_)
  rw [preparedFiniteForwardWork_eq]
  exact pow_le_pow_left₀ (by positivity)
    (add_le_add (le_preparedFiniteForwardParameter A constants stage hp) le_rfl) A

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem exists_prepared_commonRadius_densityCap_nested_bound (maxLayers : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      ∀ {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m),
      m ≤ maxLayers → ∀ M Jalloc : ℕ,
      (∀ j, Fintype.card (prep j).Coord ≤ M) →
      ∀ p : ℝ, 0 ≤ p → (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      ∀ constants : ℕ → ℕ, ∀ innerDepth outer inner : ℕ,
      4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
        (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j) ≤
          Real.exp (preparedFiniteForwardWork A constants inner
            (candidateNestedForwardSeed A constants innerDepth outer p)) := by
  obtain ⟨A₀, hA₀, hcap⟩ := exists_prepared_commonRadius_densityCap_forward_bound maxLayers
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA X J m prep hm M Jalloc hM p hp hnum V hV hprofile
    constants innerDepth outer inner
  have hAtwo : 2 ≤ A := hA₀.trans hA
  have h := hcap A hA prep hm M Jalloc hM p hp hnum V hV hprofile constants 0
  apply h.trans (Real.exp_le_exp.mpr ?_)
  rw [preparedFiniteForwardWork_eq, preparedFiniteForwardParameter_zero,
    preparedFiniteForwardWork_eq]
  apply pow_le_pow_left₀ (add_nonneg hp (Nat.cast_nonneg A))
  exact add_le_add
    ((le_candidateNestedForwardSeed A constants innerDepth outer hAtwo hp).trans
      (le_preparedFiniteForwardParameter A constants inner
        (candidateNestedForwardSeed_nonneg A constants innerDepth outer hp))) le_rfl

noncomputable def preparedCommonRadiusDensityCapNestedExponent (maxLayers : ℕ) : ℕ :=
  Classical.choose (exists_prepared_commonRadius_densityCap_nested_bound maxLayers)

theorem prepared_commonRadius_densityCap_nested_bound (maxLayers A : ℕ)
    (hA : preparedCommonRadiusDensityCapNestedExponent maxLayers ≤ A)
    {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m)
    (hm : m ≤ maxLayers) (M Jalloc : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (p : ℝ) (hp : 0 ≤ p)
    (hnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p)
    (V : Fin m → ℝ≥0) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp p)
    (constants : ℕ → ℕ) (innerDepth outer inner : ℕ) :
    4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
      (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j) ≤
        Real.exp (preparedFiniteForwardWork A constants inner
          (candidateNestedForwardSeed A constants innerDepth outer p)) :=
  (Classical.choose_spec (exists_prepared_commonRadius_densityCap_nested_bound maxLayers)).2
    A hA prep hm M Jalloc hM p hp hnum V hV hprofile constants innerDepth outer inner

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawRecoveredRationalCardinalityCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators NNReal Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

noncomputable def forecastFrozenIntegerMixedValue
    (z : ∀ j, Fin (n j) → ℤ) (v : (Σ j, J j) → ℝ) :
    ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
  fun j => ((mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
    ((EuclideanSpace.equiv (J j) ℝ).symm (fun i => v ⟨j,i⟩))).1, z j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

noncomputable def forecastRecoveredIntegerLabels (β : (Σ j, J j) → ℤ) :
    ∀ j, Fin (n j) ⊕ Eout j → ℤ :=
  fun j => standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (basis j) (hb j)
    (fun i => β ⟨j,i⟩)

noncomputable def forecastLawRecoveredRationalFactor
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) : ℝ :=
  rationalInactiveForecast law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N volume
    (fun a _ => forecastRecoveredIntegerLabels U basis hb bW β (selected a).1
      (Sum.inl (selected a).2))
    (forecastCongruenceOutput short r
      (fun j i => (forecastRecoveredIntegerLabels U basis hb bW β j i : ZMod N)))

noncomputable def forecastLawRecoveredKernel
    (v : X → ℝ) (r : X → ZMod N) (β : (Σ j, J j) → ℤ)
    (y : (Σ j, J j) → ℝ) : ℝ :=
  density (forecastNormalizedSpatialCoordinates base physicalN τ v,
    forecastNormalizedActiveCoordinates short
      (allocatedFullMixedSiteValue (R := R) U basis
        (forecastFrozenIntegerMixedValue U basis o
          (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i)) y))) *
    forecastLawRecoveredRationalFactor B U basis S law selected sample x active Y N volume hb bW r β


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawCenteredRecoveredKernel
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

variable {d : ℕ} (e : Fin d ≃ Σ j, J j) (c : (Σ j, J j) → ℝ)

def centeredTagPullback (f : ((Σ j, J j) → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun y => f (fun a => y (e.symm a) + c a)

noncomputable def forecastLawCenteredRecoveredKernel
    (v : X → ℝ) (r : X → ZMod N) (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ :=
  centeredTagPullback e c (kernel v r (fun a => β (e.symm a))) y


end Erdos3.VectorPolynomial

end

end OAI

end


