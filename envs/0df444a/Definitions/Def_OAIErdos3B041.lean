-- Prove2me | Definitions.Def_OAIErdos3B041
-- name    : OAIErdos3B041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T00:39:42.199695+00:00
-- url     : https://prove2.me/theorems/f8483eac-80b7-48c3-8d35-6a53b2b16e28
-- title:
--   OpenAI Erdős-3 split, definitions bundle 42 of 132
-- statement:
--   Definitions bundle 42 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B040`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 42 available.
--
--   Modules: `OAI.Erdos3.CircleFourier.IsometricCircleAction.project`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.project_character`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.project_eq_at`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.project_equivariant`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.project_lipschitz`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.project_norm_le`, `OAI.Erdos3.CircleFourier.exists_prescribed_circle_projection`, `OAI.Erdos3.CircleFourier.iteratedExactProjection`, `OAI.Erdos3.CircleFourier.iteratedExactProjection_character`, `OAI.Erdos3.CircleFourier.iteratedExactProjection_eq_on`, `OAI.Erdos3.CircleFourier.iteratedExactProjection_lipschitz`, `OAI.Erdos3.CircleFourier.iteratedExactProjection_norm_le`, `OAI.Erdos3.CircleFourier.real_phase_map_lipschitz`, `OAI.Erdos3.CyclicBohr.Set.approximationComplexity`, `OAI.Erdos3.CyclicBohr.Set.approximationLipBound`, `OAI.Erdos3.ExternalFamilyPrecenterProjectionData`, `OAI.Erdos3.NativeSampleCorrelation.casesOn`, `OAI.Erdos3.NativeSampleCorrelation.exists_of_expansion`, `OAI.Erdos3.NativeSampleCorrelation.mono`, `OAI.Erdos3.NativeSampleCorrelation.ofMean`, `OAI.Erdos3.NativeSampleModel`, `OAI.Erdos3.NativeSampleModel.VerticalExpansion`, `OAI.Erdos3.NativeSampleModel.VerticalExpansion.complexity`, `OAI.Erdos3.NativeSampleModel.constOne`, `OAI.Erdos3.NativeSampleModel.norm_le`, `OAI.Erdos3.NativeSampleModel.smul`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_prescribed_central_projection`, `OAI.Erdos3.OrdinaryPolynomialPhase.budget`, `OAI.Erdos3.OrdinaryPolynomialPhase.exists_niltest`, `OAI.Erdos3.OrdinaryPolynomialPhase.exists_niltest_of_degree`, `OAI.Erdos3.OrdinaryPolynomialPhase.exists_phase_orbit`, `OAI.Erdos3.OrdinaryPolynomialPhase.nilmanifold`, `OAI.Erdos3.OrdinaryPolynomialPhase.nilmanifold_geometry`, `OAI.Erdos3.OrdinaryPolynomialPhase.phaseBasisFintype`, `OAI.Erdos3.OrdinaryPolynomialPhase.specialize_rename`, `OAI.Erdos3.OrdinaryPolynomialPhase.two_le_budget`, `OAI.Erdos3.OrdinaryPolynomialPhase.weight`, `OAI.Erdos3.OrdinaryPolynomialPhase.weight_le`, `OAI.Erdos3.OrdinaryPolynomialPhase.weight_pos`, `OAI.Erdos3.PolynomialTranslationLie.centralConstantPolynomial`, `OAI.Erdos3.PolynomialTranslationLie.centralRationalElement_mem_top`, `OAI.Erdos3.PolynomialTranslationLie.centralRealLine`, `OAI.Erdos3.PolynomialTranslationLie.centralRealLine_add`, `OAI.Erdos3.PolynomialTranslationLie.centralRealLine_commute`, `OAI.Erdos3.PolynomialTranslationLie.centralRealLine_coord`, `OAI.Erdos3.PolynomialTranslationLie.centralRealLine_map`, `OAI.Erdos3.PolynomialTranslationLie.centralRealLine_zero`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBufferedNiltest`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBufferedNiltest_complexity`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBufferedNiltest_eval`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBufferedNiltest_evalReal`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBufferedObservable`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBufferedObservable_central`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBufferedObservable_lipschitz`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBufferedObservable_mk`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBufferedObservable_norm_le_one`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationTwistedNiltest`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationTwistedNiltest_complexity`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationTwistedNiltest_eval`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationTwistedNiltest_evalReal`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationTwistedObservable`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationTwistedObservable_lipschitz`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationTwistedObservable_mk`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationTwistedObservable_norm_le_one`, `OAI.Erdos3.PositiveCyclicNiltest.mul`, `OAI.Erdos3.RationalFilteredNilmanifold.KernelProjectionParameters`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeFinBasis_permute`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreePermute_coordinate_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeSpacePermute_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.commonStridePullback`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.commonStridePullback_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.commonStridePullback_lipBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.commonStridePullback_normBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.commonStridePullback_observable`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.continuous_kernelProjectionTranslation_observable`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.evalReal`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.evalReal_integer`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_external_family_common_positive_kernel_projection`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.expNormalize`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.expNormalize_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.expNormalize_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.expNormalize_norm`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.external_family_kernelProjection_tested_error`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integrable_kernelProjectionTranslation_observable`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.kernelProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.kernelProjection_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.kernelProjection_congr`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.kernelProjection_invariant`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.kernelProjection_observable_eq_integral`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.kernelProjection_observable_sub_norm_le`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.kernelProjection_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.kernelProjection_unitInterval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.phaseShift`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.phaseShift_complexity_iff`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.phaseShift_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.phaseShift_evalReal`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.phaseShift_lipBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.phaseShift_normBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.phaseShift_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.scaleComplex`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.scaleComplex_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.scaleComplex_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.scaleComplex_evalCyclic`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.scaleComplex_norm`, `OAI.Erdos3.RationalFilteredNilmanifold.continuous_kernelProjectionTranslation_act`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_bounded_niltest_pair_sum`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_externalFamily_contractive_vertical_expansion`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_external_family_centralRationalCircle_frequency`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_iteratedCentralCircle_translation`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_kernelProjectionTranslation`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_prescribed_projection`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_step_one_character`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_controlled_vertical_operators`, `OAI.Erdos3.RationalFilteredNilmanifold.externalNetNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.externalNetNiltest_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.kernelProjectionCircleFamily`, `OAI.Erdos3.RationalFilteredNilmanifold.kernelProjectionTranslation`, `OAI.Erdos3.RationalFilteredNilmanifold.kernelProjectionTranslation_act`, `OAI.Erdos3.RationalFilteredNilmanifold.kernelProjectionTranslation_central`, `OAI.Erdos3.RationalFilteredNilmanifold.kernelProjectionTranslation_mem`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeMap_dist_le`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeSpaceMap`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeSpaceMap_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeSpaceMap_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeSpaceMap_smul`, `OAI.Erdos3.RationalTorus.Algebra`, `OAI.Erdos3.RationalTorus.BottomQuotient`, `OAI.Erdos3.RationalTorus.affineNiltest`, `OAI.Erdos3.RationalTorus.affineNiltest_complexity`, `OAI.Erdos3.RationalTorus.affineNiltest_eval`, `OAI.Erdos3.RationalTorus.affineNiltest_evalCyclic`, `OAI.Erdos3.RationalTorus.affineOrbit`, `OAI.Erdos3.RationalTorus.affineOrbit_coordinates`, `OAI.Erdos3.RationalTorus.affineOrbit_phases`, `OAI.Erdos3.RationalTorus.basis`, `OAI.Erdos3.RationalTorus.basis_equivFun`, `OAI.Erdos3.RationalTorus.basis_equivFun_symm`, `OAI.Erdos3.RationalTorus.basis_layers`, `OAI.Erdos3.RationalTorus.basis_repr`, `OAI.Erdos3.RationalTorus.exists_bottom_quotient_character`, `OAI.Erdos3.RationalTorus.filtration`, `OAI.Erdos3.RationalTorus.instAddCommGroupAlgebra`, `OAI.Erdos3.RationalTorus.instLieAlgebraRatAlgebra`, `OAI.Erdos3.RationalTorus.instLieRingAlgebra`, `OAI.Erdos3.RationalTorus.instModuleRatAlgebra`, `OAI.Erdos3.RationalTorus.instRealContinuousSMul`, `OAI.Erdos3.RationalTorus.instRealT2Space`, `OAI.Erdos3.RationalTorus.instRealTopologicalAddGroup`, `OAI.Erdos3.RationalTorus.instRealTopology`, `OAI.Erdos3.RationalTorus.intervalCoordinate_lipschitz`, `OAI.Erdos3.RationalTorus.intervalOrbit`, `OAI.Erdos3.RationalTorus.intervalOrbit_phase`, `OAI.Erdos3.RationalTorus.lattice`, `OAI.Erdos3.RationalTorus.lattice_coordinates`, `OAI.Erdos3.RationalTorus.lattice_inner_grid`, `OAI.Erdos3.RationalTorus.lattice_outer_grid`, `OAI.Erdos3.RationalTorus.lie_eq_zero`, `OAI.Erdos3.RationalTorus.nilmanifold`, `OAI.Erdos3.RationalTorus.nilmanifold_geometry`, `OAI.Erdos3.RationalTorus.phaseCoordinates`, `OAI.Erdos3.RationalTorus.phaseCoordinates_inv`, `OAI.Erdos3.RationalTorus.phaseCoordinates_lattice`, `OAI.Erdos3.RationalTorus.phaseCoordinates_lipschitz`, `OAI.Erdos3.RationalTorus.phaseCoordinates_mul`, `OAI.Erdos3.RationalTorus.phaseProjection`, `OAI.Erdos3.RationalTorus.phaseProjection_lipschitz`, `OAI.Erdos3.RationalTorus.phaseProjection_mk`, `OAI.Erdos3.RationalTorus.realAffineNiltest`, `OAI.Erdos3.RationalTorus.realAffineNiltest_complexity`, `OAI.Erdos3.RationalTorus.realAffineNiltest_evalCyclic`, `OAI.Erdos3.RationalTorus.realAffineNiltest_unitInterval`, `OAI.Erdos3.RationalTorus.reindexedRealObservable`, `OAI.Erdos3.RationalTorus.reindexedRealObservable_lipschitz`, `OAI.Erdos3.RationalTorus.reindexedRealObservable_norm`, `OAI.Erdos3.RationalTorus.residueNiltest`, `OAI.Erdos3.RationalTorus.residueNiltest_complexity`, `OAI.Erdos3.RationalTorus.residueNiltest_evalCyclic`, `OAI.Erdos3.RationalTorus.residueNiltest_unit_interval`, `OAI.Erdos3.RationalTorus.residueObservable_lipschitz`, `OAI.Erdos3.RationalTorus.trivialFiltration`, `OAI.Erdos3.RationalTorus.trivialFiltration_basis_layers`, `OAI.Erdos3.RationalTorus.trivialNilmanifold`, `OAI.Erdos3.RationalTorus.trivialNilmanifold_const_one_complexity`, `OAI.Erdos3.RationalTorus.trivialNilmanifold_geometry`, `OAI.Erdos3.RationalTorus.trivial_lattice_inner_grid`, `OAI.Erdos3.RationalTorus.trivial_lattice_outer_grid`, `OAI.Erdos3.RationalTorus.zeroAlgebraSubsingleton`, `OAI.Erdos3.SymmetricEvaluationIndex`, `OAI.Erdos3.VectorPolynomial.CoefficientDeckResidues`, `OAI.Erdos3.VectorPolynomial.coefficientDeckKernelEquiv`, `OAI.Erdos3.VectorPolynomial.coefficientDeckKernelEquiv_coordinate`, `OAI.Erdos3.VectorPolynomial.coefficientKernelCoordinates`, `OAI.Erdos3.arrayResidueChart`, `OAI.Erdos3.continuous_momentProduct`, `OAI.Erdos3.detector_of_unit_detector`, `OAI.Erdos3.exists_controlled_residue_refinement`, `OAI.Erdos3.exists_cyclic_character_niltest`, `OAI.Erdos3.exists_externalFamilyPrecenterProjectionData`, `OAI.Erdos3.exists_external_family_precenter_kernel_projection_budget`, `OAI.Erdos3.exists_interval_circle_partition`, `OAI.Erdos3.exists_interval_residue_partition`, `OAI.Erdos3.exists_invariant_unit_family`, `OAI.Erdos3.exists_localMajor_dense_slice_niltest`, `OAI.Erdos3.exists_localMajor_dense_slice_niltest_early`, `OAI.Erdos3.exists_localMajor_dense_slice_niltest_nine_tenths`, `OAI.Erdos3.exists_localMajor_slice_niltest`, `OAI.Erdos3.exists_momentProduct_lower`, `OAI.Erdos3.exists_momentProduct_unit_lower`, `OAI.Erdos3.exists_sampled_native_model`, `OAI.Erdos3.exists_short_euclidean_lattice_basis`, `OAI.Erdos3.exists_symmetric_unit_family`, `OAI.Erdos3.major_phase_nine_tenths`, `OAI.Erdos3.mixedArrayReference`, `OAI.Erdos3.mixedArrayReference_sigmaFinite`, `OAI.Erdos3.mixedArrayRegroup`, `OAI.Erdos3.mixedArrayRegroup_measurePreserving`, `OAI.Erdos3.mixedPolynomialPoint`, `OAI.Erdos3.mixedScalarArrayLaw`, `OAI.Erdos3.mixedScalarArrayLaw_regroup`, `OAI.Erdos3.momentLowerConstant`, `OAI.Erdos3.momentLowerConstant_bound`, `OAI.Erdos3.momentLowerConstant_pos`, `OAI.Erdos3.momentProduct_smul`, `OAI.Erdos3.nativeTorusLocalLift`, `OAI.Erdos3.nativeTorusLocalLift_mk`, `OAI.Erdos3.nativeTorusProjection`, `OAI.Erdos3.orthonormalArrayChart`, `OAI.Erdos3.orthonormalChart`, `OAI.Erdos3.orthonormalChart_measurePreserving`, `OAI.Erdos3.orthonormalChart_norm_le`, `OAI.Erdos3.orthonormalChart_symm_norm_le`, `OAI.Erdos3.orthonormalCoordinateLattice`, `OAI.Erdos3.orthonormalCoordinateLattice_covolume`, `OAI.Erdos3.orthonormalCoordinateLattice_discrete`, `OAI.Erdos3.orthonormalCoordinateLattice_full`, `OAI.Erdos3.orthonormalMixedChart`, `OAI.Erdos3.orthonormalMixedChart_measurePreserving`, `OAI.Erdos3.orthonormalMixedDensity`, `OAI.Erdos3.orthonormalMixedDensity_law`, `OAI.Erdos3.orthonormalMixedDensity_measurable`, `OAI.Erdos3.orthonormalMixedDensity_nonneg`, `OAI.Erdos3.refine_positive_partition_by_residue`, `OAI.Erdos3.residue_indicator_positiveCyclicNiltest`, `OAI.Erdos3.symmetricEvaluation`, `OAI.Erdos3.symmetricEvaluationIndex_card`, `OAI.Erdos3.symmetricEvaluationLip`, `OAI.Erdos3.symmetricEvaluationRadius`, `OAI.Erdos3.symmetricEvaluationRadius_pos`, `OAI.Erdos3.symmetricEvaluation_const_mul`, `OAI.Erdos3.symmetricEvaluation_lower`, `OAI.Erdos3.symmetricEvaluation_metric`, `OAI.Erdos3.symmetricEvaluation_permute`, `OAI.Erdos3.symmetricEvaluation_smul`, `OAI.Erdos3.symmetricUnitBudget`, `OAI.Erdos3.symmetricUnitBudget_bounds`, `OAI.Erdos3.symmetricUnitConstant`, `OAI.Erdos3.symmetricUnitFamilyLip`, `OAI.Erdos3.torusPhaseLinear`, `OAI.Erdos3.torusPhaseLinear_eq_of_small`, `OAI.Erdos3.torusPhaseLinear_inv`, `OAI.Erdos3.torusPhaseLinear_mul`, `OAI.Erdos3.torusPhaseLinear_tmul`, `OAI.Erdos3.torusPhase_lattice_map`, `OAI.Erdos3.torus_reindex_lipschitz`, `OAI.Erdos3.twistedNativeSampleFunctions`, `OAI.Erdos3.twistedNativeSampleFunctions_balanced`, `OAI.Erdos3.twistedNativeSampleFunctions_norm`, `OAI.Erdos3.twistedNativeSampleFunctions_zero`, `OAI.Erdos3.zeroDegreePolynomialPhaseNiltest`, `OAI.Erdos3.zeroDegreePolynomialPhaseNiltest_normBound`, `_private.Estimates.ExternalPhysicalMemberPivotMasks.0.OAI.Erdos3.RationalFilteredNilmanifold.contractiveFamily_integer_error`, `_private.Estimates.ExternalPhysicalMemberPivotMasks.0.OAI.Erdos3.RationalFilteredNilmanifold.contractiveFamily_real_error`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B036
import Definitions.Def_OAIErdos3B106

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricEvaluationLowerBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem continuous_momentProduct (m : ℕ) :
    Continuous (fun v : Fin m → Fin m → ℂ => momentProduct v) := by
  unfold momentProduct
  fun_prop

theorem exists_momentProduct_unit_lower (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin m → Fin m → ℂ,
      (∀ i, ‖v i‖ = 1) → c ≤ ‖momentProduct v‖ := by
  have hcompact : IsCompact {v : Fin m → Fin m → ℂ | ∀ i, ‖v i‖ = 1} := by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      isCompact_pi_infinite (fun _i : Fin m => isCompact_sphere (0 : Fin m → ℂ) 1)
  apply hcompact.exists_forall_le' ((continuous_momentProduct m).norm.continuousOn)
  intro v hv
  apply norm_pos_iff.mpr
  obtain ⟨z, hz⟩ := momentProduct_ne_zero_some v (fun i hi => by
    have h := hv i
    simp only [hi, norm_zero, zero_ne_one] at h)
  intro h
  exact hz (congrFun h z)

theorem momentProduct_smul {m : ℕ} (v : Fin m → Fin m → ℂ) (c : Fin m → ℂ) :
    momentProduct (fun i => c i • v i) = (∏ i, c i) • momentProduct v := by
  funext z
  simp only [momentProduct, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum, Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_momentProduct_lower (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin m → Fin m → ℂ,
      (∀ i, v i ≠ 0) → ∃ z, c * ∏ i, ‖v i‖ ≤ ‖momentProduct v z‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_momentProduct_unit_lower m
  refine ⟨c, hc, ?_⟩
  intro v hv
  let w : Fin m → Fin m → ℂ := fun i => (‖v i‖ : ℂ)⁻¹ • v i
  have hn (i) : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr (hv i)
  have hnc (i) : (‖v i‖ : ℂ) ≠ 0 := by exact_mod_cast hn i
  have hw (i) : ‖w i‖ = 1 := by
    simp only [w, norm_smul, norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (hn i)
  have hreconstruct : (fun i => (‖v i‖ : ℂ) • w i) = v := by
    funext i
    simp only [w, smul_smul, mul_inv_cancel₀ (hnc i), one_smul]
  have hex : ∃ z, c ≤ ‖momentProduct w z‖ := by
    by_contra h
    push Not at h
    exact not_lt_of_ge (hbound w hw) ((pi_norm_lt_iff hc).mpr h)
  obtain ⟨z, hz⟩ := hex
  refine ⟨z, ?_⟩
  have heq : ‖momentProduct v z‖ = (∏ i, ‖v i‖) * ‖momentProduct w z‖ := by
    have h := congrFun (momentProduct_smul w (fun i => (‖v i‖ : ℂ))) z
    rw [hreconstruct] at h
    rw [h, Pi.smul_apply, norm_smul, norm_prod]
    simp only [Complex.norm_real, norm_norm]
  rw [heq, mul_comm c]
  exact mul_le_mul_of_nonneg_left hz (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))

noncomputable def momentLowerConstant (m : ℕ) : ℝ :=
  Classical.choose (exists_momentProduct_lower m)

theorem momentLowerConstant_pos (m : ℕ) : 0 < momentLowerConstant m :=
  (Classical.choose_spec (exists_momentProduct_lower m)).1

theorem momentLowerConstant_bound {m : ℕ} (v : Fin m → Fin m → ℂ)
    (hv : ∀ i, v i ≠ 0) :
    ∃ z, momentLowerConstant m * ∏ i, ‖v i‖ ≤ ‖momentProduct v z‖ :=
  (Classical.choose_spec (exists_momentProduct_lower m)).2 v hv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev SymmetricEvaluationIndex (m : ℕ) (I : Type*) := (Fin m → I) × Fin (m * m + 1)

noncomputable def symmetricEvaluation {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (k : SymmetricEvaluationIndex m I) : ℂ :=
  momentProduct (fun i j => v i (k.1 j)) k.2

theorem symmetricEvaluation_permute {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (e : Equiv.Perm (Fin m)) :
    symmetricEvaluation (fun i => v (e i)) = symmetricEvaluation v := by
  funext k
  exact Equiv.prod_comp e (fun i => ∑ j, v i (k.1 j) * (k.2.val : ℂ) ^ j.val)

theorem symmetricEvaluation_smul {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (c : Fin m → ℂ) :
    symmetricEvaluation (fun i => c i • v i) = (∏ i, c i) • symmetricEvaluation v := by
  funext k
  exact congrFun (momentProduct_smul (fun i j => v i (k.1 j)) c) k.2

theorem symmetricEvaluation_const_mul {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (c : ℂ) (k : SymmetricEvaluationIndex m I) :
    symmetricEvaluation (fun i j => c * v i j) k = c ^ m * symmetricEvaluation v k := by
  have h := congrFun (symmetricEvaluation_smul v (fun _ => c)) k
  change symmetricEvaluation (fun i => c • v i) k = _
  simpa only [Pi.smul_apply, smul_eq_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

theorem symmetricEvaluationIndex_card (m : ℕ) (I : Type*) [Fintype I] :
    Fintype.card (SymmetricEvaluationIndex m I) = Fintype.card I ^ m * (m * m + 1) := by
  simp only [SymmetricEvaluationIndex, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem symmetricEvaluation_lower {m : ℕ} {I : Type*} [Fintype I]
    (v : Fin m → I → ℂ) (hv : ∀ i, ∑ j, ‖v i j‖ ^ 2 = 1) :
    ∃ k, momentLowerConstant m / (Fintype.card I + 1 : ℝ) ^ m ≤
      ‖symmetricEvaluation v k‖ := by
  classical
  choose a ha using fun i => exists_large_unit_coordinate (v i) (hv i)
  let w : Fin m → Fin m → ℂ := fun i j => v i (a j)
  let δ : ℝ := 1 / (Fintype.card I + 1 : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hw (i) : δ ≤ ‖w i‖ := (ha i).trans (norm_le_pi_norm (w i) i)
  have hw0 (i) : w i ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hw i))
  obtain ⟨z, hz⟩ := momentLowerConstant_bound w hw0
  refine ⟨(a, z), ?_⟩
  have hprod : δ ^ m ≤ ∏ i, ‖w i‖ := by
    have h := Finset.prod_le_prod (s := Finset.univ)
      (fun _ _ => hδ.le) (fun i _ => hw i)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  calc
    _ = momentLowerConstant m * δ ^ m := by simp [δ, div_eq_mul_inv, inv_pow]
    _ ≤ momentLowerConstant m * ∏ i, ‖w i‖ :=
      mul_le_mul_of_nonneg_left hprod (momentLowerConstant_pos m).le
    _ ≤ ‖symmetricEvaluation v (a, z)‖ := hz

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymmetricEvaluationMetric
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def symmetricEvaluationLip (m : ℕ) (K : ℝ≥0) : ℝ≥0 :=
  m * ((momentWeightBound m : ℝ≥0) * K) * (momentWeightBound m : ℝ≥0) ^ m

theorem symmetricEvaluation_metric {m : ℕ} {I X : Type*} [PseudoMetricSpace X]
    (f : Fin m → I → X → ℂ) {K : ℝ≥0}
    (hf : ∀ i j, LipschitzWith K (f i j)) (hn : ∀ i j x, ‖f i j x‖ ≤ 1)
    (k : SymmetricEvaluationIndex m I) :
    (∀ x, ‖symmetricEvaluation (fun i j => f i j x) k‖ ≤ (momentWeightBound m : ℝ) ^ m) ∧
      LipschitzWith (symmetricEvaluationLip m K)
        (fun x => symmetricEvaluation (fun i j => f i j x) k) := by
  have hB : (1 : ℝ≥0) ≤ momentWeightBound m := by exact_mod_cast momentWeightBound_pos m
  have h := bounded_lipschitz_fintype_prod
    (fun i x => momentLinear (fun j => f i (k.1 j) x) k.2) hB
    (fun i => momentLinear_lipschitz _ (fun j => hf i (k.1 j)) k.2)
    (fun i x => by simpa only [mul_one, NNReal.coe_natCast] using
      norm_momentLinear_le (fun j => f i (k.1 j) x) k.2 zero_le_one (fun j => hn i (k.1 j) x))
  simpa only [Fintype.card_fin, symmetricEvaluationLip, NNReal.coe_natCast,
    symmetricEvaluation, momentProduct, momentLinear] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InvariantUnitFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def symmetricEvaluationRadius (m n : ℕ) : ℝ≥0 :=
  ⟨momentLowerConstant m / (n + 1 : ℝ) ^ m, by
    have := momentLowerConstant_pos m
    positivity⟩

theorem symmetricEvaluationRadius_pos (m n : ℕ) : 0 < symmetricEvaluationRadius m n := by
  change 0 < momentLowerConstant m / (n + 1 : ℝ) ^ m
  have := momentLowerConstant_pos m
  positivity

noncomputable def symmetricUnitFamilyLip (m n : ℕ) (K : ℝ≥0) : ℝ≥0 :=
  2 / symmetricEvaluationRadius m n *
    ((n ^ m * (m * m + 1) + 1 : ℝ≥0) * symmetricEvaluationLip m K)

theorem exists_symmetric_unit_family {m : ℕ} {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (f : Fin m → I → X → ℂ) {K : ℝ≥0}
    (hf : ∀ i j, LipschitzWith K (f i j))
    (hunit : ∀ i x, ∑ j, ‖f i j x‖ ^ 2 = 1) :
    ∃ g : SymmetricEvaluationIndex m I → X → ℂ,
      (∀ x, ∑ k, ‖g k x‖ ^ 2 = 1) ∧ (∀ k x, ‖g k x‖ ≤ 1) ∧
      (∀ k, LipschitzWith (symmetricUnitFamilyLip m (Fintype.card I) K) (g k)) ∧
      ∀ x y (c : ℂ) (e : Equiv.Perm (Fin m)), ‖c‖ = 1 →
        (∀ i j, f i j x = c * f (e i) j y) → ∀ k, g k x = c ^ m * g k y := by
  have hnorm (i j x) : ‖f i j x‖ ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => ‖f i j x‖ ^ 2) (fun j _ => sq_nonneg ‖f i j x‖) (Finset.mem_univ j)
    rw [hunit] at h
    nlinarith [norm_nonneg (f i j x)]
  let u (k : SymmetricEvaluationIndex m I) (x : X) := symmetricEvaluation (fun i j => f i j x) k
  have hlower (x) : ∃ k, (symmetricEvaluationRadius m (Fintype.card I) : ℝ) ≤ ‖u k x‖ :=
    symmetricEvaluation_lower (fun i j => f i j x) (fun i => hunit i x)
  obtain ⟨g, hgunit, hgnorm, hglip, hgphase⟩ := exists_normalized_complex_family u
    (symmetricEvaluationRadius_pos m (Fintype.card I))
    (fun k => (symmetricEvaluation_metric f hf hnorm k).2) hlower
  refine ⟨g, hgunit, hgnorm, ?_, ?_⟩
  · intro k
    simpa only [symmetricUnitFamilyLip, symmetricEvaluationIndex_card,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hglip k
  · intro x y c e hc hxy k
    apply hgphase x y (c ^ m) (by rw [norm_pow, hc, one_pow]) _ k
    intro a
    change symmetricEvaluation (fun i j => f i j x) a =
      c ^ m * symmetricEvaluation (fun i j => f i j y) a
    simp_rw [hxy]
    rw [symmetricEvaluation_const_mul]
    exact congrArg (fun z => c ^ m * z)
      (congrFun (symmetricEvaluation_permute (fun i j => f i j y) e) a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_invariant_unit_family {Γ I X : Type*} [Group Γ] [Fintype Γ]
    [Fintype I] [PseudoMetricSpace X] [MulAction Γ X]
    (f : I → X → ℂ) {K A : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j))
    (hunit : ∀ x, ∑ j, ‖f j x‖ ^ 2 = 1)
    (hact : ∀ a : Γ, LipschitzWith A (fun x : X => a • x)) :
    ∃ g : SymmetricEvaluationIndex (Fintype.card Γ) I → X → ℂ,
      (∀ x, ∑ k, ‖g k x‖ ^ 2 = 1) ∧ (∀ k x, ‖g k x‖ ≤ 1) ∧
      (∀ k, LipschitzWith
        (symmetricUnitFamilyLip (Fintype.card Γ) (Fintype.card I) (K * A)) (g k)) ∧
      (∀ a : Γ, ∀ k x, g k (a • x) = g k x) ∧
      ∀ x y (c : ℂ), ‖c‖ = 1 → (∀ a : Γ, ∀ j, f j (a • x) = c * f j (a • y)) →
        ∀ k, g k x = c ^ Fintype.card Γ * g k y := by
  classical
  let e := (Fintype.equivFin Γ).symm
  let F (i : Fin (Fintype.card Γ)) (j : I) (x : X) := f j (e i • x)
  obtain ⟨g, hgunit, hgnorm, hglip, hgphase⟩ := exists_symmetric_unit_family F
    (fun i j => (hf j).comp (hact (e i))) (fun i x => hunit (e i • x))
  refine ⟨g, hgunit, hgnorm, hglip, ?_, ?_⟩
  · intro a k x
    let ε : Equiv.Perm (Fin (Fintype.card Γ)) := e.trans ((Equiv.mulRight a).trans e.symm)
    have he (i) : e (ε i) = e i * a := by simp [ε]
    have h := hgphase (a • x) x 1 ε (by simp) (fun i j => by
      change f j (e i • (a • x)) = 1 * f j (e (ε i) • x)
      rw [he, mul_smul, one_mul]) k
    simpa only [one_pow, one_mul] using h
  · intro x y c hc hxy k
    exact hgphase x y c (Equiv.refl _) hc (fun i j => hxy (e i) j) k

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SymmetricUnitBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def symmetricUnitConstant (m : ℕ) : ℕ :=
  ⌈2 / momentLowerConstant m⌉₊ + m * m + 2 + (m + 1) * momentWeightBound m

noncomputable def symmetricUnitBudget (m : ℕ) (p : ℝ) : ℝ :=
  (2 * m + 2 : ℝ) * (p + 1) + symmetricUnitConstant m

theorem symmetricUnitBudget_bounds (m n : ℕ) (K : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) :
    ((n ^ m * (m * m + 1) : ℕ) : ℝ) ≤ Real.exp (symmetricUnitBudget m p) ∧
      (symmetricUnitFamilyLip m n K : ℝ) ≤ Real.exp (symmetricUnitBudget m p) := by
  let D := ⌈2 / momentLowerConstant m⌉₊
  let B := momentWeightBound m
  have hc := momentLowerConstant_pos m
  have hnplus : (n + 1 : ℝ) ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hexp := Real.one_le_exp hp
    nlinarith
  have hnpow : (n : ℝ) ^ m ≤ Real.exp ((m : ℝ) * p) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg n) hn m
  have hnpowplus : (n + 1 : ℝ) ^ m ≤ Real.exp ((m : ℝ) * (p + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hnplus m
  have hd : 2 / momentLowerConstant m ≤ Real.exp D :=
    (Nat.le_ceil _).trans (by linarith [Real.add_one_le_exp (D : ℝ)])
  have hout : (n : ℝ) ^ m * (m * m + 1) + 1 ≤ Real.exp ((m : ℝ) * p + (m * m + 2)) := by
    rw [Real.exp_add]
    have hcoef : (m * m + 2 : ℝ) ≤ Real.exp (m * m + 2 : ℝ) := by
      linarith [Real.add_one_le_exp (m * m + 2 : ℝ)]
    have hmul := mul_le_mul_of_nonneg_right hnpow (by positivity : (0 : ℝ) ≤ m * m + 1)
    have heone := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg m) hp)
    nlinarith
  have hradius : 2 / (symmetricEvaluationRadius m n : ℝ) ≤
      Real.exp ((D : ℝ) + m * (p + 1)) := by
    change 2 / (momentLowerConstant m / (n + 1 : ℝ) ^ m) ≤ _
    rw [Real.exp_add]
    calc
      _ = (2 / momentLowerConstant m) * (n + 1 : ℝ) ^ m := by field_simp
      _ ≤ _ := mul_le_mul hd hnpowplus (by positivity) (Real.exp_pos _).le
  have hB : (B : ℝ) ≤ Real.exp B := by linarith [Real.add_one_le_exp (B : ℝ)]
  have hBpow : (B : ℝ) ^ (m + 1) ≤ Real.exp ((m + 1 : ℝ) * B) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg B) hB (m + 1)
    rw [← Real.exp_nat_mul] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hraw : (symmetricEvaluationLip m K : ℝ) ≤
      Real.exp ((m : ℝ) + (m + 1) * B + p) := by
    change (m : ℝ) * ((B : ℝ) * K) * (B : ℝ) ^ m ≤ _
    rw [Real.exp_add, Real.exp_add]
    calc
      _ = (m : ℝ) * (B : ℝ) ^ (m + 1) * K := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul
        (by linarith [Real.add_one_le_exp (m : ℝ)]) hBpow (by positivity) (Real.exp_pos _).le)
        hK K.coe_nonneg (by positivity)
  have htotal : (symmetricUnitFamilyLip m n K : ℝ) ≤ Real.exp
      ((D : ℝ) + m * (p + 1) + (m * p + (m * m + 2)) + (m + (m + 1) * B + p)) := by
    change (2 / (symmetricEvaluationRadius m n : ℝ)) *
      (((n : ℝ) ^ m * (m * m + 1) + 1) * (symmetricEvaluationLip m K : ℝ)) ≤ _
    calc
      _ ≤ Real.exp ((D : ℝ) + m * (p + 1)) *
          (Real.exp (m * p + (m * m + 2)) * Real.exp (m + (m + 1) * B + p)) :=
        mul_le_mul hradius (mul_le_mul hout hraw (by positivity) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hbudget : (D : ℝ) + m * (p + 1) + (m * p + (m * m + 2)) +
      (m + (m + 1) * B + p) ≤ symmetricUnitBudget m p := by
    dsimp [symmetricUnitBudget, symmetricUnitConstant, D, B]
    push_cast
    nlinarith
  constructor
  · have hle : (m : ℝ) * p + (m * m + 2) ≤ symmetricUnitBudget m p := by
      dsimp [symmetricUnitBudget, symmetricUnitConstant]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) ⌈2 / momentLowerConstant m⌉₊,
        Nat.cast_nonneg (α := ℝ) (momentWeightBound m)]
    push_cast
    exact (le_add_of_nonneg_right zero_le_one).trans (hout.trans (Real.exp_le_exp.mpr hle))
  · exact htotal.trans (Real.exp_le_exp.mpr hbudget)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquarefreeActionMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem nativeMap_dist_le
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {s t d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hlattice : D.lattice ≤ E.lattice.comap (mapOfSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hφ : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p)
    (u v : D.RealGroup) :
    letI := D.metricSpace
    letI := E.metricSpace
    dist (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ u) : E.Space)
      (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ v)) ≤
          Real.exp ((p + 3) ^ 2) * dist (QuotientGroup.mk u : D.Space) (QuotientGroup.mk v) := by
  let := D.metricSpace
  let := E.metricSpace
  let := realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
  let := realificationQuotientMetricSpace E.basis E.lattice E.grid E.grid_pos E.outer_grid
  obtain ⟨K, _, hK, hLip⟩ := exists_realificationMap_quotient_lipschitz_exp_bound
    D.basis E.basis φ D.lattice E.lattice hlattice
    D.grid E.grid D.grid_pos E.grid_pos D.outer_grid E.outer_grid ⌈Real.exp p⌉₊
    (by linarith : 0 ≤ p + 1)
    (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
    (by simpa only [Fintype.card_fin] using hE.1.trans (by linarith : p ≤ p + 1))
    (ceil_exp_le_exp_add_one hp) (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  have hd := hLip.dist_le_mul (QuotientGroup.mk u) (QuotientGroup.mk v)
  change dist (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ u) : E.Space)
    (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ v)) ≤
        (K : ℝ) * dist (QuotientGroup.mk u : D.Space) (QuotientGroup.mk v) at hd
  apply hd.trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  simpa only [show p + 1 + 2 = p + 3 by ring] using hK

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeFinBasis_permute (p : ℝ) (e : ReplicatedPermutation bound)
    (j : Fin (Fintype.card M.SquarefreeBasisIndex)) :
    ∃ k, M.filtration.replicatedLiePermute e (M.squarefreeFinBasis p j) = M.squarefreeFinBasis p k := by
  obtain ⟨k, hk⟩ := M.squarefreeBasis_permute p (replicatedPermutation bound e)
    (replicatedPermutation_block bound e) ((Fintype.equivFin M.SquarefreeBasisIndex).symm j)
  refine ⟨Fintype.equivFin M.SquarefreeBasisIndex k, ?_⟩
  simpa only [squarefreeFinBasis, Basis.reindex_apply, Equiv.symm_apply_apply,
    MultidegreeLieFiltration.replicatedLiePermute] using hk

theorem squarefreePermute_coordinate_height (p : ℝ) (e : ReplicatedPermutation bound)
    {q : ℝ} (hq : 0 ≤ q) (i j : Fin (Fintype.card M.SquarefreeBasisIndex)) :
    rationalLogHeight ((M.squarefreeFinBasis p).repr
      (M.filtration.replicatedLiePermute e (M.squarefreeFinBasis p j)) i) ≤ q := by
  obtain ⟨k, hk⟩ := M.squarefreeFinBasis_permute p e j
  rw [hk]
  simp only [Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simpa [rationalLogHeight] using hq

variable (p : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]

theorem squarefreeSpacePermute_lipschitz {q : ℝ} (hq : 0 ≤ q)
    (hE : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q)
    (e : ReplicatedPermutation bound) :
    letI := (M.squarefreeModel p B hB hstable).metricSpace
    LipschitzWith ⟨Real.exp ((q + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.squarefreeSpacePermute p B hB hstable e) := by
  let := (M.squarefreeModel p B hB hstable).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le (M.squarefreeModel p B hB hstable) (M.squarefreeModel p B hB hstable)
        (M.filtration.replicatedLiePermute e).toLieHom
        (fun g hg => (M.squarefreeLattice_permute p B hstable (replicatedPermutation bound e)
          (replicatedPermutation_block bound e) g).mpr hg)
        hq hE hE (M.squarefreePermute_coordinate_height p e hq) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSpaceMap
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

noncomputable def nativeSpaceMap : D.Space → E.Space :=
  cosetMap D.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
    (realificationMap_subgroup φ D.lattice E.lattice hφ)

theorem nativeSpaceMap_mk (x : D.RealGroup) :
    D.nativeSpaceMap E φ hφ (QuotientGroup.mk x) =
      QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ x) := rfl

theorem nativeSpaceMap_smul (z : D.RealGroup) (x : D.Space) :
    D.nativeSpaceMap E φ hφ (z • x) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ z • D.nativeSpaceMap E φ hφ x :=
  cosetMap_smul _ _ _ _ z x

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

theorem nativeSpaceMap_lipschitz {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hentries : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) :
    letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ (D.nativeSpaceMap E φ hφ) := by
  let := D.metricSpace
  let := E.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  exact D.nativeMap_dist_le E φ hφ hp hD hE hentries u v

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open Module

def Algebra (d : ℕ) := Fin d → ℚ

instance (d : ℕ) : AddCommGroup (Algebra d) :=
  inferInstanceAs (AddCommGroup (Fin d → ℚ))

instance (d : ℕ) : Module ℚ (Algebra d) :=
  inferInstanceAs (Module ℚ (Fin d → ℚ))

instance (d : ℕ) : LieRing (Algebra d) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (Fin d → ℚ))
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

instance (d : ℕ) : LieAlgebra ℚ (Algebra d) where
  toModule := inferInstanceAs (Module ℚ (Fin d → ℚ))
  lie_smul _ _ _ := by
    change (0 : Algebra d) = _ • (0 : Algebra d)
    exact (smul_zero _).symm

theorem lie_eq_zero {d : ℕ} (x y : Algebra d) : ⁅x, y⁆ = 0 := rfl

noncomputable def basis (d : ℕ) : Basis (Fin d) ℚ (Algebra d) := by
  change Basis (Fin d) ℚ (Fin d → ℚ)
  exact Pi.basisFun ℚ (Fin d)

theorem basis_repr (d : ℕ) (x : Algebra d) (i : Fin d) : (basis d).repr x i = x i := by
  change Fin d → ℚ at x
  exact Pi.basisFun_repr ℚ (Fin d) x i

theorem basis_equivFun (d : ℕ) (x : Algebra d) : (basis d).equivFun x = x := by
  ext i
  exact basis_repr d x i

theorem basis_equivFun_symm (d : ℕ) (x : Fin d → ℚ) : (basis d).equivFun.symm x = x := by
  have h := basis_equivFun d ((basis d).equivFun.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

def filtration (d : ℕ) : NilpotentLieFiltration (Algebra d) 1 where
  layer j := if j ≤ 1 then ⊤ else ⊥
  antitone := by
    intro i j hij
    by_cases hj : j ≤ 1
    · have hi := hij.trans hj
      simp only [hi, hj, ite_true, le_refl]
    · simp only [hj, ite_false, bot_le]
  one_eq_top := by simp
  lie_mem := by
    intro i j a b _ _
    rw [lie_eq_zero]
    exact Submodule.zero_mem _
  terminal := by simp

theorem basis_layers (d j : ℕ) :
    (filtration d).layer j = Submodule.span ℚ ((basis d) '' {_i : Fin d | j ≤ (1 : ℕ)}) := by
  by_cases hj : j ≤ 1
  · simpa only [filtration, hj, ite_true, Set.ofPred_true, Set.image_univ] using (basis d).span_eq.symm
  · simp only [filtration, hj, ite_false, Set.ofPred_false, Set.image_empty, Submodule.span_empty]

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_step_one_character :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ f : D.Space → ℂ,
        (letI := D.metricSpace; LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ f) ∧
        (∀ x, ‖f x‖ = 1) ∧
        ∀ z : D.RealGroup, f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z := by
  obtain ⟨C, hC, hseed⟩ := exists_native_central_seed 1
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  let := D.metricSpace
  obtain ⟨K, hK, f, hLip, _, heq⟩ := hseed D hp hD η hη hint
  have heq' (z : D.RealGroup) : f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z :=
    heq z (by rw [D.filtration.realification.subgroup_one]; trivial)
  refine ⟨f, hLip.weaken hK, ?_, heq'⟩
  intro x
  induction x using Quotient.inductionOn with
  | h z => rw [heq', logCharacter_norm]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalTorus

open Module

noncomputable def lattice (d : ℕ) : Subgroup (filtration d).Group where
  carrier := {g | IntegralVector g.coord}
  one_mem' := ⟨0, fun _ => rfl⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨z, hz⟩ := ha
    obtain ⟨w, hw⟩ := hb
    refine ⟨z + w, ?_⟩
    intro i
    rw [(filtration d).stepOne_coord_mul]
    change a.coord i + b.coord i = ((z + w) i : ℚ)
    simp only [Pi.add_apply, Int.cast_add, hz, hw]
  inv_mem' := by
    intro a ha
    obtain ⟨z, hz⟩ := ha
    refine ⟨-z, ?_⟩
    intro i
    change -(a.coord i) = ((-z) i : ℚ)
    simp only [Pi.neg_apply, Int.cast_neg, hz]

theorem lattice_coordinates (d : ℕ) :
    bchSubgroupCoordinates (basis d) (lattice d) = {x | IntegralVector x} := by
  ext x
  change IntegralVector ((basis d).equivFun.symm x) ↔ IntegralVector x
  rw [basis_equivFun_symm]

theorem lattice_inner_grid (d : ℕ) :
    scaledIntegerGrid 1 ⊆ bchSubgroupCoordinates (basis d) (lattice d) := by
  rw [lattice_coordinates]
  rintro x ⟨z, rfl⟩
  exact ⟨z, fun i => by simp⟩

theorem lattice_outer_grid (d : ℕ) :
    bchSubgroupCoordinates (basis d) (lattice d) ⊆ denominatorGrid 1 := by
  rw [lattice_coordinates]
  intro x hx
  simpa only [denominatorGrid, Set.mem_ofPred_eq, Nat.cast_one, one_smul] using hx

noncomputable def nilmanifold (d : ℕ) : RationalFilteredNilmanifold (Algebra d) 1 d :=
  (filtration d).ofAdaptedBasis (basis d) (fun _ => 1) (basis_layers d)
    (lattice d) 1 (by decide) (lattice_inner_grid d) (lattice_outer_grid d)

theorem nilmanifold_geometry (d : ℕ) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (nilmanifold d).GeometryComplexityLE p := by
  apply (filtration d).ofAdaptedBasis_geometry (basis d) (fun _ => 1) (basis_layers d)
    (lattice d) 1 (by decide) (lattice_inner_grid d) (lattice_outer_grid d) hp hd
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · intro i j k
    simpa [lieStructureConstants, lie_eq_zero, rationalLogHeight] using hp

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open scoped TensorProduct

noncomputable instance instRealTopology (d : ℕ) : TopologicalSpace (ℝ ⊗[ℚ] Algebra d) :=
  moduleTopology ℝ (ℝ ⊗[ℚ] Algebra d)

instance instRealTopologicalAddGroup (d : ℕ) : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d) :=
  IsModuleTopology.topologicalAddGroup ℝ _

instance instRealContinuousSMul (d : ℕ) : ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d) :=
  ModuleTopology.continuousSMul ℝ _

instance instRealT2Space (d : ℕ) : T2Space (ℝ ⊗[ℚ] Algebra d) :=
  realification_moduleTopology_t2 (basis d)

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open scoped TensorProduct

noncomputable def phaseCoordinates (d : ℕ) (g : (nilmanifold d).RealGroup) :
    Fin d → CircleFourier.Circle :=
  fun i => (((basis d).baseChange ℝ).repr g.coord i : CircleFourier.Circle)

theorem phaseCoordinates_mul (d : ℕ) (g h : (nilmanifold d).RealGroup) :
    phaseCoordinates d (g * h) = phaseCoordinates d g + phaseCoordinates d h := by
  ext i
  simp only [phaseCoordinates, (nilmanifold d).filtration.realification.stepOne_coord_mul,
    map_add, Finsupp.add_apply, AddCircle.coe_add, Pi.add_apply]

theorem phaseCoordinates_inv (d : ℕ) (g : (nilmanifold d).RealGroup) :
    phaseCoordinates d g⁻¹ = -phaseCoordinates d g := by
  ext i
  simp [phaseCoordinates]

theorem phaseCoordinates_lattice (d : ℕ) (g : (nilmanifold d).RealGroup)
    (hg : g ∈ (nilmanifold d).realLattice) : phaseCoordinates d g = 0 := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨z, hz⟩ : IntegralVector a.coord := ha
  ext i
  change ((((basis d).baseChange ℝ).equivFun
    (NilpotentLieBCHGroup.realificationHom a).coord) i : CircleFourier.Circle) = 0
  rw [NilpotentLieBCHGroup.realificationHom_coordinates]
  dsimp only
  rw [basis_repr, hz]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨z i, ?_⟩
  simp

noncomputable def phaseProjection (d : ℕ) :
    (nilmanifold d).Space → (Fin d → CircleFourier.Circle) :=
  Quotient.lift (phaseCoordinates d) (fun a b hab => by
    have h := phaseCoordinates_lattice d (a⁻¹ * b) (QuotientGroup.leftRel_apply.mp hab)
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [phaseCoordinates_mul, phaseCoordinates_inv, sub_eq_add_neg, add_comm] using h)

@[simp] theorem phaseProjection_mk (d : ℕ) (g : (nilmanifold d).RealGroup) :
    phaseProjection d (QuotientGroup.mk g) = phaseCoordinates d g := rfl

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct NNReal

abbrev BottomQuotient (d : ℕ) := Algebra d ⧸ (⊥ : LieIdeal ℚ (Algebra d))

theorem exists_bottom_quotient_character :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d : ℕ)
      [TopologicalSpace (ℝ ⊗[ℚ] BottomQuotient d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] BottomQuotient d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] BottomQuotient d)]
      [T2Space (ℝ ⊗[ℚ] BottomQuotient d)] (i₀ : Fin d) {p : ℝ},
      0 ≤ p → (d : ℝ) ≤ p →
      ∃ (e : ℕ) (E : RationalFilteredNilmanifold (BottomQuotient d) 1 e),
        E.GeometryComplexityLE p ∧
        (∀ i j, rationalLogHeight (E.basis.repr
          (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) (basis d j)) i) ≤ p) ∧
        ∃ (η : BottomQuotient d →ₗ[ℚ] ℚ) (V : E.Space → ℂ),
          (∀ x, η (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) x) = x i₀) ∧
          (letI := E.metricSpace;
            LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ V) ∧
          (∀ x, ‖V x‖ = 1) ∧
          ∀ z : E.RealGroup, V (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z := by
  obtain ⟨C, hC, hcharacter⟩ := exists_native_step_one_character
  refine ⟨C, hC, ?_⟩
  intro d _ _ _ _ i₀ p hp hd
  classical
  have hI : (filtration d).layer (1 + 1) ≤ (⊥ : LieIdeal ℚ (Algebra d)).toSubmodule := by
    rw [(filtration d).terminal]
    exact bot_le
  have hspan : (⊥ : LieIdeal ℚ (Algebra d)).toSubmodule =
      Submodule.span ℚ (basis d '' (∅ : Set (Fin d))) := by simp
  let E := (filtration d).coordinateQuotientModel (basis d) (fun _ => 1) (basis_layers d)
    (⊥ : LieIdeal ℚ (Algebra d)) hI ∅ hspan (lattice d) 1 (by decide)
    (lattice_inner_grid d) (lattice_outer_grid d)
  have hE : E.GeometryComplexityLE p := by
    apply (filtration d).coordinateQuotientModel_geometry (basis d) (fun _ => 1) (basis_layers d)
      (⊥ : LieIdeal ℚ (Algebra d)) hI ∅ hspan (lattice d) 1 (by decide)
      (lattice_inner_grid d) (lattice_outer_grid d) hp
    · simpa only [Fintype.card_fin] using hd
    · simpa only [Nat.cast_one] using Real.one_le_exp hp
    · intro i j k
      simpa [lieStructureConstants, lie_eq_zero, rationalLogHeight] using hp
  let η : BottomQuotient d →ₗ[ℚ] ℚ :=
    (⊥ : Submodule ℚ (Algebra d)).liftQ ((basis d).coord i₀) bot_le
  have hη (x : Algebra d) : η (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) x) = x i₀ :=
    basis_repr d x i₀
  have hproj (i) (j) : rationalLogHeight (E.basis.repr
      (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) (basis d j)) i) ≤ p := by
    change rationalLogHeight (((supportedQuotientBasis (basis d)
      (⊥ : Submodule ℚ (Algebra d)) ∅ hspan).reindex (Fintype.equivFin _)).repr
        ((⊥ : Submodule ℚ (Algebra d)).mkQ (basis d j)) i) ≤ p
    rw [Basis.repr_reindex_apply, supportedQuotientBasis_repr_mk]
    exact rationalLogHeight_le_of_height (basis_repr_height_one _ _ _)
      (by simpa only [Nat.cast_one] using Real.one_le_exp hp)
  have hheight (i) : rationalLogHeight (η (E.basis i)) ≤ p := by
    change rationalLogHeight (η (((supportedQuotientBasis (basis d)
      (⊥ : Submodule ℚ (Algebra d)) ∅ hspan).reindex (Fintype.equivFin _)) i)) ≤ p
    rw [Basis.reindex_apply, supportedQuotientBasis_apply]
    change rationalLogHeight ((basis d).repr (basis d _) i₀) ≤ p
    exact rationalLogHeight_le_of_height (basis_repr_height_one _ _ _)
      (by simpa only [Nat.cast_one] using Real.one_le_exp hp)
  have hint : ∀ z : E.RealGroup, z ∈ E.realLattice →
      ∃ n : ℤ, realifyFunctional η z.coord = n := by
    apply E.realLattice_functional_integral η
    intro z hz
    obtain ⟨g, hg, rfl⟩ := hz
    obtain ⟨a, ha⟩ := hg
    refine ⟨a i₀, ?_⟩
    change η (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) g.coord) = _
    rw [hη]
    exact ha i₀
  obtain ⟨V, hLip, hnorm, heq⟩ := hcharacter E hp hE η hheight hint
  exact ⟨_, E, hE, hproj, η, V, hη, hLip, hnorm, heq⟩

end Erdos3.RationalTorus

end

section

namespace Erdos3.CircleFourier

theorem real_phase_map_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith 1 (fun v : ι → ℝ => fun i => (v i : Circle)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg dist_nonneg).mpr
  intro i
  change ‖(v i : Circle) - (w i : Circle)‖ ≤ dist v w
  calc
    _ = ‖((v i - w i : ℝ) : Circle)‖ := rfl
    _ ≤ ‖v i - w i‖ := QuotientAddGroup.norm_mk_le_norm
    _ = dist (v i) (w i) := rfl
    _ ≤ dist v w := dist_le_pi_dist v w i

end Erdos3.CircleFourier

namespace Erdos3.RationalTorus

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable (d : ℕ)
  [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]

theorem phaseCoordinates_lipschitz :
    letI := rightMetricSpace
      (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
      ((basis d).baseChange ℝ)
    LipschitzWith 1 (phaseCoordinates d) := by
  let := rightMetricSpace
    (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
    ((basis d).baseChange ℝ)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc := ((nilmanifold d).filtration.realification.stepOne_coordinates_lipschitz
    ((basis d).baseChange ℝ)).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, basisHomeomorph_apply] at hc
  have hphase : dist (phaseCoordinates d x) (phaseCoordinates d y) ≤
      dist (((basis d).baseChange ℝ).equivFun x.coord)
        (((basis d).baseChange ℝ).equivFun y.coord) := by
    change dist
      (fun i : Fin d => (((basis d).baseChange ℝ).repr x.coord i : CircleFourier.Circle))
      (fun i : Fin d => (((basis d).baseChange ℝ).repr y.coord i : CircleFourier.Circle)) ≤ _
    simpa only [NNReal.coe_one, one_mul, Basis.equivFun_apply] using
      CircleFourier.real_phase_map_lipschitz.dist_le_mul
        (((basis d).baseChange ℝ).equivFun x.coord)
        (((basis d).baseChange ℝ).equivFun y.coord)
  simpa only [NNReal.coe_one, one_mul] using hphase.trans hc

theorem phaseProjection_lipschitz :
    letI := (nilmanifold d).metricSpace
    LipschitzWith 1 (phaseProjection d) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] Algebra d) :=
    ((basis d).baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
    ((basis d).baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
    ((basis d).baseChange ℝ)
  exact rightCosetMetricSpace_lipschitz_lift (nilmanifold d).realLattice
    (nilmanifold d).realLattice_closed_discrete.1 (phaseProjection d)
    (phaseCoordinates_lipschitz d)

end Erdos3.RationalTorus

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t : ℕ}

noncomputable def torusPhaseLinear (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (Fin t → ℝ) :=
  ((RationalTorus.basis t).baseChange ℝ).equivFun.toLinearMap.comp (φ.toLinearMap.baseChange ℝ)

theorem torusPhaseLinear_tmul (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
    (a : ℝ) (x : L) (i : Fin t) :
    torusPhaseLinear φ (a ⊗ₜ[ℚ] x) i = a * (φ x i : ℝ) := by
  change ((RationalTorus.basis t).baseChange ℝ).repr
    (φ.toLinearMap.baseChange ℝ (a ⊗ₜ[ℚ] x)) i = _
  rw [LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul, RationalTorus.basis_repr]
  simpa [Algebra.smul_def] using mul_comm (φ x i : ℝ) a

variable (D : RationalFilteredNilmanifold L s d) (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)

theorem torusPhaseLinear_mul (g h : D.RealGroup) :
    torusPhaseLinear φ (g * h).coord = torusPhaseLinear φ g.coord + torusPhaseLinear φ h.coord := by
  let f := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot) φ
  change ((RationalTorus.basis t).baseChange ℝ).equivFun (f (g * h)).coord =
    ((RationalTorus.basis t).baseChange ℝ).equivFun (f g).coord +
      ((RationalTorus.basis t).baseChange ℝ).equivFun (f h).coord
  rw [f.map_mul, (RationalTorus.nilmanifold t).filtration.realification.stepOne_coord_mul, map_add]

theorem torusPhaseLinear_inv (g : D.RealGroup) :
    torusPhaseLinear φ g⁻¹.coord = -torusPhaseLinear φ g.coord :=
  (torusPhaseLinear φ).map_neg g.coord

variable (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))

include hphase in
theorem torusPhase_lattice_map :
    D.lattice ≤ (RationalTorus.nilmanifold t).lattice.comap
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot) φ) := by
  intro z hz
  exact hphase z hz

noncomputable def nativeTorusProjection : D.Space → (Fin t → CircleFourier.Circle) :=
  (RationalTorus.phaseProjection t) ∘
    D.nativeSpaceMap (RationalTorus.nilmanifold t) φ (torusPhase_lattice_map D φ hphase)

noncomputable def nativeTorusLocalLift : D.Space → (Fin t → ℝ) :=
  centeredTorusLift ∘ nativeTorusProjection D φ hphase

theorem nativeTorusLocalLift_mk (g : D.RealGroup)
    (hg : ∀ i, |torusPhaseLinear φ g.coord i| ≤ 1 / 4) :
    nativeTorusLocalLift D φ hphase (QuotientGroup.mk g) = torusPhaseLinear φ g.coord := by
  funext i
  exact centeredCircleLift_coe (hg i)

include hphase in
theorem torusPhaseLinear_eq_of_small (g h : D.RealGroup)
    (hg : ∀ i, |torusPhaseLinear φ g.coord i| ≤ 1 / 4)
    (hh : ∀ i, |torusPhaseLinear φ h.coord i| ≤ 1 / 4)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h) :
    torusPhaseLinear φ g.coord = torusPhaseLinear φ h.coord := by
  rw [← nativeTorusLocalLift_mk D φ hphase g hg, ← nativeTorusLocalLift_mk D φ hphase h hh, heq]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3

end

section

namespace Erdos3.RationalTorus

open scoped BigOperators TensorProduct NNReal

variable {σ : Type*} [Fintype σ] (d : ℕ)

noncomputable def affineOrbit (b : Fin d → ℝ) (a : σ → Fin d → ℝ) :
    (nilmanifold d).filtration.realification.PolynomialOrbit (fun _ : σ => 1) :=
  (nilmanifold d).filtration.realification.affinePolynomialOrbit
    (((basis d).baseChange ℝ).equivFun.symm b)
    (fun j => ((basis d).baseChange ℝ).equivFun.symm (a j))

theorem affineOrbit_coordinates (b : Fin d → ℝ) (a : σ → Fin d → ℝ) (x : σ → ℤ) :
    ((basis d).baseChange ℝ).equivFun
        ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (affineOrbit d b a)).coord =
      b + ∑ j, (x j : ℝ) • a j := by
  unfold affineOrbit
  rw [NilpotentLieFiltration.affinePolynomialOrbit_integer_coord, map_add, map_sum]
  simp only [map_smul, LinearEquiv.apply_symm_apply]

theorem affineOrbit_phases (b : Fin d → ℝ) (a : σ → Fin d → ℝ) (x : σ → ℤ) :
    phaseCoordinates d
        ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (affineOrbit d b a)) =
      fun i => ((b + ∑ j, (x j : ℝ) • a j) i : CircleFourier.Circle) := by
  change (fun i => (((basis d).baseChange ℝ).equivFun
    ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
      (affineOrbit d b a)).coord i : CircleFourier.Circle)) = _
  rw [affineOrbit_coordinates]

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]
  (b : Fin d → ℝ) (a : σ → Fin d → ℝ)
  (Ψ : (Fin d → CircleFourier.Circle) → ℂ) (M K : ℝ≥0)
  (hΨ : ∀ v, ‖Ψ v‖ ≤ M) (hLip : LipschitzWith K Ψ)

noncomputable def affineNiltest : (nilmanifold d).Niltest (fun _ : σ => 1) where
  orbit := affineOrbit d b a
  observable := Ψ ∘ phaseProjection d
  normBound := M
  lipBound := K
  norm_le x := hΨ (phaseProjection d x)
  lipschitz := by
    let := (nilmanifold d).metricSpace
    simpa only [mul_one] using hLip.comp (phaseProjection_lipschitz d)

theorem affineNiltest_eval (x : σ → ℤ) :
    (affineNiltest d b a Ψ M K hΨ hLip).eval x =
      Ψ (fun i => ((b + ∑ j, (x j : ℝ) • a j) i : CircleFourier.Circle)) := by
  change Ψ (phaseCoordinates d
    ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
      (affineOrbit d b a))) = _
  rw [affineOrbit_phases]

theorem affineNiltest_evalCyclic (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (affineNiltest d b a Ψ M K hΨ hLip).evalCyclic N x =
      Ψ (fun i => ((b + ∑ j, ((x j).val : ℝ) • a j) i : CircleFourier.Circle)) := by
  rw [RationalFilteredNilmanifold.Niltest.evalCyclic, affineNiltest_eval]
  simp only [Int.cast_natCast]

theorem affineNiltest_complexity {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hbudget : Real.log (2 + (M : ℝ) + (K : ℝ)) ≤ p) :
    (affineNiltest d b a Ψ M K hΨ hLip).ComplexityLE p :=
  ⟨nilmanifold_geometry d hp hd, hbudget⟩

end Erdos3.RationalTorus

end

section

namespace Erdos3

open RationalFilteredNilmanifold CircleFourier
open scoped TensorProduct NNReal

theorem exists_cyclic_character_niltest {N : ℕ} [NeZero N] (χ : AddChar (ZMod N) ℂ) :
    ∃ T : (RationalTorus.nilmanifold 1).Niltest (fun _ : Unit => 1),
      T.normBound ≤ 1 ∧ T.ComplexityLE 12 ∧
      ∀ x : ZMod N, T.evalCyclic N (fun _ => x) = χ x := by
  obtain ⟨r, hr⟩ := AddChar.zmodAddEquiv.surjective χ
  obtain ⟨theta, htheta⟩ := CyclicBohr.exists_real_frequency_phase r
  have hphase (x : ZMod N) :
      character (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) = χ x := by
    rw [htheta]
    exact congrArg (fun ψ : AddChar (ZMod N) ℂ => ψ x) hr
  let Ψ : (Fin 1 → CircleFourier.Circle) → ℂ := fun v => character (v 0)
  have hΨ (v) : ‖Ψ v‖ ≤ (1 : ℝ≥0) := by
    exact le_of_eq (norm_character (v 0))
  have hLip : LipschitzWith characterLipConstant Ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (character_lipschitz.dist_le_mul (x 0) (y 0)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y 0) characterLipConstant.coe_nonneg)
  let T := RationalTorus.affineNiltest 1 0 (fun _ : Unit => fun _ => theta)
    Ψ 1 characterLipConstant hΨ hLip
  have hT : T.ComplexityLE 12 := by
    apply RationalTorus.affineNiltest_complexity 1 0 (fun _ : Unit => fun _ => theta)
      Ψ 1 characterLipConstant hΨ hLip (by norm_num) (by norm_num)
    change Real.log (2 + 1 + 2 * Real.pi) ≤ 12
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + 1 + 2 * Real.pi)
    linarith [Real.pi_lt_four]
  refine ⟨T, le_rfl, hT, ?_⟩
  intro x
  simpa [T, Ψ, RationalTorus.affineNiltest_evalCyclic] using hphase x

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct NNReal

theorem torus_reindex_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι → κ) :
    LipschitzWith 1 (fun v : κ → CircleFourier.Circle => fun i => v (e i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg dist_nonneg).mpr
  intro i
  change ‖v (e i) - w (e i)‖ ≤ dist v w
  rw [← dist_eq_norm]
  exact dist_le_pi_dist v w (e i)

namespace RationalTorus

variable {ι : Type*} [Fintype ι] {d : ℕ} (e : ι ≃ Fin d)
  (Ψ : (ι → CircleFourier.Circle) → ℝ)

noncomputable def reindexedRealObservable : (Fin d → CircleFourier.Circle) → ℂ :=
  fun v => (Ψ (fun i => v (e i)) : ℂ)

omit [Fintype ι] in
theorem reindexedRealObservable_norm (hΨ : ∀ v, 0 ≤ Ψ v ∧ Ψ v ≤ 1)
    (v : Fin d → CircleFourier.Circle) : ‖reindexedRealObservable e Ψ v‖ ≤ (1 : ℝ≥0) := by
  change ‖(Ψ (fun i => v (e i)) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hΨ _).1]
  exact (hΨ _).2

theorem reindexedRealObservable_lipschitz {K : ℝ≥0} (hLip : LipschitzWith K Ψ) :
    LipschitzWith K (reindexedRealObservable e Ψ) := by
  change LipschitzWith K (fun v : Fin d → CircleFourier.Circle => (Ψ (fun i => v (e i)) : ℂ))
  simpa only [one_mul, mul_one, Function.comp_def] using
    Complex.isometry_ofReal.lipschitz.comp (hLip.comp (torus_reindex_lipschitz e))

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]
  (b a : ι → ℝ) (K : ℝ≥0)
  (hΨ : ∀ v, 0 ≤ Ψ v ∧ Ψ v ≤ 1) (hLip : LipschitzWith K Ψ)

noncomputable def realAffineNiltest : (nilmanifold d).Niltest (fun _ : Unit => 1) :=
  affineNiltest d (fun i => b (e.symm i)) (fun _ : Unit => fun i => a (e.symm i))
    (reindexedRealObservable e Ψ) 1 K (reindexedRealObservable_norm e Ψ hΨ)
    (reindexedRealObservable_lipschitz e Ψ hLip)

theorem realAffineNiltest_unitInterval :
    (realAffineNiltest e Ψ b a K hΨ hLip).UnitIntervalValued := by
  intro z
  change 0 = 0 ∧ 0 ≤ Ψ (fun i => phaseProjection d z (e i)) ∧
    Ψ (fun i => phaseProjection d z (e i)) ≤ 1
  exact ⟨rfl, hΨ _⟩

theorem realAffineNiltest_evalCyclic (N : ℕ) [NeZero N] (x : ZMod N) :
    (realAffineNiltest e Ψ b a K hΨ hLip).evalCyclic N (fun _ => x) =
      (Ψ (fun i => ((b i + (x.val : ℝ) * a i : ℝ) : CircleFourier.Circle)) : ℂ) := by
  unfold realAffineNiltest
  rw [affineNiltest_evalCyclic]
  simp [reindexedRealObservable]

theorem realAffineNiltest_complexity {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hbudget : Real.log (3 + (K : ℝ)) ≤ p) :
    (realAffineNiltest e Ψ b a K hΨ hLip).ComplexityLE p := by
  apply affineNiltest_complexity _ _ _ _ _ _ _ _ hp hd
  simpa only [NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num] using hbudget

end RationalTorus
end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

noncomputable def approximationLipBound (B : Set N) (rho : ℝ≥0) : ℝ≥0 :=
  ((B.rank : ℝ≥0) * (B.approximationWidth rho)⁻¹) * CircleFourier.characterLipConstant

noncomputable def approximationComplexity (B : Set N) (rho : ℝ≥0) : ℝ :=
  max (B.rank : ℝ) (Real.log (3 + (B.approximationLipBound rho : ℝ)))

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanShortLatticeBasis
namespace OAI

section

namespace Erdos3

open Module MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthonormalChart (b : OrthonormalBasis I ℝ E) : (I → ℝ) ≃L[ℝ] E :=
  (EuclideanSpace.equiv I ℝ).symm.trans b.repr.toContinuousLinearEquiv.symm

omit [FiniteDimensional ℝ E] in
theorem orthonormalChart_norm_le (b : OrthonormalBasis I ℝ E) (x : I → ℝ) :
    ‖orthonormalChart b x‖ ≤ (Fintype.card I : ℝ) * ‖x‖ := by
  change ‖b.repr.symm ((EuclideanSpace.equiv I ℝ).symm x)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ∑ i, |x i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _i : I, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    _ = _ := by simp

omit [FiniteDimensional ℝ E] in
theorem orthonormalChart_symm_norm_le (b : OrthonormalBasis I ℝ E) (x : E) :
    ‖(orthonormalChart b).symm x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  have h := PiLp.norm_apply_le (b.repr x) i
  simpa [orthonormalChart] using h

noncomputable def orthonormalCoordinateLattice (Λ : Submodule ℤ E)
    (b : OrthonormalBasis I ℝ E) : Submodule ℤ (I → ℝ) :=
  ZLattice.comap ℝ Λ (orthonormalChart b).toLinearMap

instance orthonormalCoordinateLattice_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (b : OrthonormalBasis I ℝ E) : DiscreteTopology (orthonormalCoordinateLattice Λ b) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ Λ (orthonormalChart b).toLinearMap))

instance orthonormalCoordinateLattice_full (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : OrthonormalBasis I ℝ E) :
    IsZLattice ℝ (orthonormalCoordinateLattice Λ b) :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ Λ (orthonormalChart b).toLinearMap))

variable [MeasurableSpace E] [BorelSpace E]

theorem orthonormalChart_measurePreserving (b : OrthonormalBasis I ℝ E) :
    MeasurePreserving (orthonormalChart b) :=
  b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp I)

theorem orthonormalCoordinateLattice_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : OrthonormalBasis I ℝ E) :
    ZLattice.covolume (orthonormalCoordinateLattice Λ b) = ZLattice.covolume Λ :=
  ZLattice.covolume_comap Λ volume volume (orthonormalChart_measurePreserving b)

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory BohrLattice.MinkowskiSecondBox
open scoped BigOperators

theorem exists_short_euclidean_lattice_basis {E A : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (o : OrthonormalBasis (Fin n) ℝ E) (v : A → E) {R : ℝ}
    (hspan : span ℝ (Set.range v) = ⊤) (hmem : ∀ a, v a ∈ Λ)
    (hnorm : ∀ a, ‖v a‖ ≤ R) :
    ∃ b : Basis (Fin n) ℝ E,
      span ℤ (Set.range b) = Λ ∧
      (∏ i, ‖b i‖) ≤ (n : ℝ) ^ n * minkowskiSecondConstant n * ZLattice.covolume Λ ∧
      ∀ i, ‖b i‖ ≤ (n : ℝ) * n.factorial * minkowskiSecondConstant n * R := by
  classical
  let e := orthonormalChart o
  let L := orthonormalCoordinateLattice Λ o
  let B := IsZLattice.basis L
  let b₀ := B.ofZLatticeBasis ℝ L
  let u := fun a => e.symm (v a)
  have huSpan : span ℝ (Set.range u) = ⊤ := by
    change span ℝ (Set.range (e.symm.toLinearMap ∘ v)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, hspan, Submodule.map_top]
    exact e.symm.toLinearEquiv.range
  have huMem : ∀ a, u a ∈ span ℤ (Set.range b₀) := by
    intro a
    rw [show span ℤ (Set.range b₀) = L from B.ofZLatticeBasis_span ℝ L]
    change e (e.symm (v a)) ∈ Λ
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hmem a
  have huNorm : ∀ a, ‖u a‖ ≤ R := fun a =>
    (orthonormalChart_symm_norm_le o (v a)).trans (hnorm a)
  obtain ⟨c, hcSpan, hcProd, hcNorm⟩ := exists_short_same_lattice_basis b₀ u huSpan huMem huNorm
  let b := c.map e.toLinearEquiv
  have hb (i) : b i = e (c i) := by simp [b]
  have hmap : L.map (e.toLinearMap.restrictScalars ℤ) = Λ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e (e.symm y) ∈ Λ
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
  have hbSpan : span ℤ (Set.range b) = Λ := by
    calc
      _ = (span ℤ (Set.range c)).map (e.toLinearMap.restrictScalars ℤ) := by
        rw [Submodule.map_span, ← Set.range_comp]
        congr 2
      _ = L.map (e.toLinearMap.restrictScalars ℤ) := by
        rw [hcSpan, show span ℤ (Set.range b₀) = L from B.ofZLatticeBasis_span ℝ L]
      _ = Λ := hmap
  have hdet : |(Matrix.of c).det| = ZLattice.covolume Λ := by
    calc
      _ = |(Matrix.of b₀).det| := abs_det_eq_of_same_integer_span c b₀ hcSpan
      _ = ZLattice.covolume L := by
        have hb₀ : (b₀ : Fin n → Fin n → ℝ) = fun i => (B i : Fin n → ℝ) :=
          funext (fun i => Basis.ofZLatticeBasis_apply ℝ L B i)
        rw [hb₀]
        exact (ZLattice.covolume_eq_det L B).symm
      _ = ZLattice.covolume Λ := orthonormalCoordinateLattice_covolume Λ o
    rfl
  have hbNorm (i) : ‖b i‖ ≤ (n : ℝ) * ‖c i‖ := by
    rw [hb]
    simpa only [Fintype.card_fin] using orthonormalChart_norm_le o (c i)
  refine ⟨b, hbSpan, ?_, ?_⟩
  · calc
      _ ≤ ∏ i, (n : ℝ) * ‖c i‖ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hbNorm i)
      _ = (n : ℝ) ^ n * ∏ i, ‖c i‖ := by simp [Finset.prod_mul_distrib]
      _ ≤ (n : ℝ) ^ n * (minkowskiSecondConstant n * ZLattice.covolume Λ) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
        simpa only [hdet] using hcProd
      _ = _ := by ring
  · intro i
    calc
      _ ≤ (n : ℝ) * ‖c i‖ := hbNorm i
      _ ≤ (n : ℝ) * ((n.factorial : ℝ) * minkowskiSecondConstant n * R) :=
        mul_le_mul_of_nonneg_left (hcNorm i) (Nat.cast_nonneg _)
      _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.OrthonormalMixedLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I] [Fintype J]

noncomputable def orthonormalMixedChart (b : OrthonormalBasis I ℝ E) :
    ((I → ℝ) × (J → ℤ)) ≃ᵐ (E × (J → ℤ)) :=
  (orthonormalChart b).toHomeomorph.toMeasurableEquiv.prodCongr (MeasurableEquiv.refl _)

theorem orthonormalMixedChart_measurePreserving (b : OrthonormalBasis I ℝ E) :
    MeasurePreserving (orthonormalMixedChart (J := J) b)
      ((volume : Measure (I → ℝ)).prod Measure.count) (volume.prod Measure.count) :=
  (orthonormalChart_measurePreserving b).prod (MeasurePreserving.id Measure.count)

noncomputable def orthonormalMixedDensity (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (p : J → PMF ℤ) (x : E × (J → ℤ)) : ℝ :=
  mixedCoefficientDensity c w p ((orthonormalMixedChart b).symm x)

omit [FiniteDimensional ℝ E] in
theorem orthonormalMixedDensity_measurable (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (p : J → PMF ℤ) : Measurable (orthonormalMixedDensity b c w p) := by
  have hf : Measurable (mixedCoefficientDensity c w p) :=
    binaryDensity_measurable (affineProductProfile_contDiff c w).continuous.measurable
      (measurable_of_countable (fun z : J → ℤ => ∏ j, (p j (z j)).toReal))
  exact hf.comp (orthonormalMixedChart b).symm.measurable

omit [FiniteDimensional ℝ E] in
theorem orthonormalMixedDensity_nonneg (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) (x) :
    0 ≤ orthonormalMixedDensity b c w p x := mixedCoefficientDensity_nonneg c w hw p _

theorem orthonormalMixedDensity_law (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    Measure.map (orthonormalMixedChart b) (mixedCoefficientLaw c w p) =
      realDensityMeasure (volume.prod Measure.count) (orthonormalMixedDensity b c w p) := by
  rw [mixedCoefficientLaw_count_density c w hw p,
    realDensityMeasure_map_equiv (orthonormalMixedChart b),
    (orthonormalMixedChart_measurePreserving b).map_eq]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedPolynomialChart
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

noncomputable def mixedPolynomialPoint (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W) (e : J → V →₀ ℕ)
    (a : I → J → ℝ) (z : Fin n → J → ℤ) (x : V → ℝ) : EuclideanSpace ℝ D :=
  (normalizedOrthogonalChart W b).symm
    (orthonormalChart o (fun i => MvPolynomial.eval x (monomialArrayPolynomial e (a i))),
      fun i => MvPolynomial.eval x
        (monomialArrayPolynomial e (fun j => (z i j : ℝ) / basisAxisScale b i)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

def mixedArrayRegroup (I Z J : Type*) :
    ((I → J → ℝ) × (Z → J → ℤ)) ≃ᵐ (J → (I → ℝ) × (Z → ℤ)) :=
  ((finiteArrayTranspose I J ℝ).prodCongr (finiteArrayTranspose Z J ℤ)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (I → ℝ) (Z → ℤ) J).symm

theorem mixedArrayRegroup_measurePreserving {I Z J : Type*}
    [Fintype I] [Fintype Z] [Fintype J]
    (μ : I → J → Measure ℝ) (ν : Z → J → Measure ℤ)
    [∀ i j, SigmaFinite (μ i j)] [∀ z j, SigmaFinite (ν z j)] :
    MeasurePreserving (mixedArrayRegroup I Z J)
      ((Measure.pi (fun i => Measure.pi (μ i))).prod (Measure.pi (fun z => Measure.pi (ν z))))
      (Measure.pi (fun j => (Measure.pi (fun i => μ i j)).prod (Measure.pi (fun z => ν z j)))) := by
  have h₁ := (finiteArrayTranspose_measurePreserving μ).prod (finiteArrayTranspose_measurePreserving ν)
  have h₂ := (measurePreserving_arrowProdEquivProdArrow (I → ℝ) (Z → ℤ) J
    (fun j => Measure.pi (fun i => μ i j)) (fun j => Measure.pi (fun z => ν z j))).symm
      (MeasurableEquiv.arrowProdEquivProdArrow (I → ℝ) (Z → ℤ) J)
  exact h₂.comp h₁

noncomputable def mixedScalarArrayLaw {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (p : Z → J → PMF ℤ) : Measure ((I → J → ℝ) × (Z → J → ℤ)) :=
  (Measure.pi (fun i => Measure.pi (fun j => affineCoefficientMeasure (c i j) (w i j)))).prod
    (Measure.pi (fun z => Measure.pi (fun j => (p z j).toMeasure)))

theorem mixedScalarArrayLaw_regroup {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    Measure.map (mixedArrayRegroup I Z J) (mixedScalarArrayLaw c w p) =
      Measure.pi (fun j => mixedCoefficientLaw (fun i => c i j) (fun i => w i j) (fun z => p z j)) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  exact (mixedArrayRegroup_measurePreserving (fun i j => affineCoefficientMeasure (c i j) (w i j))
    (fun z j => (p z j).toMeasure)).map_eq

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators ENNReal

noncomputable def mixedArrayReference (I Z O : Type*) [Fintype I] [Fintype O] :
    Measure ((I → O → ℝ) × (Z → O → ℤ)) :=
  (volume : Measure (I → O → ℝ)).prod (Measure.count : Measure (Z → O → ℤ))

instance mixedArrayReference_sigmaFinite (I Z O : Type*) [Fintype I] [Fintype Z] [Fintype O] :
    SigmaFinite (mixedArrayReference I Z O) := by
  unfold mixedArrayReference
  infer_instance

variable {E I Z O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Fintype Z] (o : OrthonormalBasis I ℝ E)

noncomputable def orthonormalArrayChart :
    ((I → O → ℝ) × (Z → O → ℤ)) ≃ᵐ (O → E × (Z → ℤ)) :=
  (mixedArrayRegroup I Z O).trans
    (MeasurableEquiv.piCongrRight (fun _ : O => orthonormalMixedChart (J := Z) o))

variable [Fintype O]

noncomputable def arrayResidueChart {R : Type*} [MeasurableSpace R] :
    (((I → O → ℝ) × (Z → O → ℤ)) × (O → R)) ≃ᵐ (O → (E × (Z → ℤ)) × R) :=
  ((orthonormalArrayChart o).prodCongr (MeasurableEquiv.refl _)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (E × (Z → ℤ)) R O).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} {m : ℕ} {J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev CoefficientDeckResidues (B : Fin m → Type*) (d : ℕ) :=
  ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) → B j → ZMod d

noncomputable def coefficientKernelCoordinates (d : ℕ) :
    (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker ≃+
      ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) →
        (quotientIntegerCover
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d).ker :=
  (nsmulKernelCongr (G := CoefficientTorus (K := K) U)
    (H := EuclideanCoefficientLayers (K := K) U) (euclideanCoefficientEquiv (K := K) U) d).trans
    ((nsmulKernelPiEquiv (fun j : Fin m => BoundedCoefficientExponent K (j.val + 1) →
        euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) d).trans
      (AddEquiv.piCongrRight fun j => nsmulKernelPiEquiv
        (fun _ : BoundedCoefficientExponent K (j.val + 1) => euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) d))

variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

noncomputable def coefficientDeckKernelEquiv (d : ℕ) (hd : 0 < d) :
    CoefficientDeckResidues (K := K) B d ≃+
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker :=
  (AddEquiv.piCongrRight fun j : Fin m => AddEquiv.piCongrRight
    fun _ : BoundedCoefficientExponent K (j.val + 1) =>
      coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd).trans (coefficientKernelCoordinates U d).symm

theorem coefficientDeckKernelEquiv_coordinate (d : ℕ) (hd : 0 < d)
    (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U (coefficientDeckKernelEquiv U bW d hd r).val j e =
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (r j e)).val := by
  change euclideanCoefficientEquiv U ((euclideanCoefficientEquiv U).symm _) j e = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def scaleComplex (T : D.Niltest w) (c : ℂ) : D.Niltest w where
  orbit := T.orbit
  observable := fun x => c * T.observable x
  normBound := ‖c‖₊ * T.normBound
  lipBound := ‖c‖₊ * T.lipBound
  norm_le x := by
    simpa only [norm_mul, NNReal.coe_mul, coe_nnnorm] using
      mul_le_mul_of_nonneg_left (T.norm_le x) (norm_nonneg c)
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← mul_sub, norm_mul, NNReal.coe_mul, coe_nnnorm, mul_assoc] using
      mul_le_mul_of_nonneg_left (T.lipschitz.dist_le_mul x y) (norm_nonneg c)

theorem scaleComplex_eval (T : D.Niltest w) (c : ℂ) (x : σ → ℤ) :
    (T.scaleComplex c).eval x = c * T.eval x := rfl

theorem scaleComplex_evalCyclic (T : D.Niltest w) (c : ℂ) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.scaleComplex c).evalCyclic N x = c * T.evalCyclic N x := rfl

theorem scaleComplex_norm (T : D.Niltest w) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (T.scaleComplex c).normBound ≤ T.normBound := by
  change ‖c‖₊ * T.normBound ≤ T.normBound
  exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast hc)

theorem scaleComplex_complexity (T : D.Niltest w) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.scaleComplex c).ComplexityLE p := by
  refine ⟨hT.1, ?_⟩
  change Real.log (2 + ‖c‖ * (T.normBound : ℝ) + ‖c‖ * (T.lipBound : ℝ)) ≤ p
  have hn := mul_le_mul_of_nonneg_right hc T.normBound.coe_nonneg
  have hl := mul_le_mul_of_nonneg_right hc T.lipBound.coe_nonneg
  exact (Real.log_le_log (by positivity) (by linarith)).trans hT.2

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct Manifold ContDiff

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def evalReal (T : D.Niltest w) (x : σ → ℝ) : ℂ :=
  T.observable (QuotientGroup.mk (D.filtration.realification.polynomialOrbitRealEval w x T.orbit))

theorem evalReal_integer (T : D.Niltest w) (x : σ → ℤ) :
    T.evalReal (fun i => (x i : ℝ)) = T.eval x := by
  unfold evalReal eval
  rw [NilpotentLieFiltration.polynomialOrbitRealEval_integer]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def expNormalize (T : D.Niltest w) (p : ℝ) : D.Niltest w :=
  T.scaleComplex (Real.exp (-p) : ℂ)

theorem expNormalize_norm (T : D.Niltest w) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.expNormalize p).normBound ≤ 1 := by
  have hb := T.observable_budget hT
  have hl := T.lipBound.coe_nonneg
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by linarith
  change ‖(Real.exp (-p) : ℂ)‖₊ * T.normBound ≤ 1
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul, coe_nnnorm, NNReal.coe_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
  calc
    _ ≤ Real.exp (-p) * Real.exp p := mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem expNormalize_complexity (T : D.Niltest w) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.expNormalize p).ComplexityLE p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  apply T.scaleComplex_complexity _ hT
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem expNormalize_eval (T : D.Niltest w) (p : ℝ) (x : σ → ℤ) :
    (T.expNormalize p).eval x = (Real.exp (-p) : ℂ) * T.eval x := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_bounded_niltest_pair_sum {J σ L K : Type*} [Fintype J] [Nonempty J]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold K t e) (w : σ → ℕ)
    (gD : D.filtration.realification.PolynomialOrbit w)
    (gE : E.filtration.realification.PolynomialOrbit w)
    (A : J → D.Niltest w) (B : J → E.Niltest w) (c : J → ℂ) {p : ℝ}
    (hAnorm : ∀ j, (A j).normBound ≤ 1) (hBnorm : ∀ j, (B j).normBound ≤ 1)
    (hA : ∀ j, (A j).ComplexityLE p) (hB : ∀ j, (B j).ComplexityLE p)
    (hAg : ∀ j, (A j).orbit = gD) (hBg : ∀ j, (B j).orbit = gE)
    (hc : ∀ j, ‖c j‖ ≤ 2) :
    ∃ N : ℕ, 0 < N ∧ N = 2 * Fintype.card J ∧
      ∃ (A' : Fin N → D.Niltest w) (B' : Fin N → E.Niltest w),
        (∀ j, (A' j).normBound ≤ 1) ∧ (∀ j, (B' j).normBound ≤ 1) ∧
        (∀ j, (A' j).ComplexityLE p) ∧ (∀ j, (B' j).ComplexityLE p) ∧
        (∀ j, (A' j).orbit = gD) ∧ (∀ j, (B' j).orbit = gE) ∧
        ∀ x, ∑ j, (A' j).eval x * (B' j).eval x =
          ∑ j, ((A j).eval x * (B j).eval x) * c j := by
  classical
  let f := (Fintype.equivFin (Bool × J)).symm
  let A' (j : Fin (Fintype.card (Bool × J))) :=
    (A (f j).2).scaleComplex (c (f j).2 / 2)
  let B' (j : Fin (Fintype.card (Bool × J))) := B (f j).2
  refine ⟨Fintype.card (Bool × J), Fintype.card_pos, ?_, A', B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_bool]
  · intro j
    exact ((A (f j).2).scaleComplex_norm (norm_complex_half_le_one (hc (f j).2))).trans (hAnorm _)
  · intro j
    exact hBnorm _
  · intro j
    exact (A (f j).2).scaleComplex_complexity (norm_complex_half_le_one (hc (f j).2)) (hA _)
  · intro j
    exact hB _
  · intro j
    exact hAg _
  · intro j
    exact hBg _
  · intro x
    exact (f.sum_comp (fun j => (c j.2 / 2 * (A j.2).eval x) * (B j.2).eval x)).trans
      (sum_double_half_products (fun j => (A j).eval x) (fun j => (B j).eval x) c)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def phaseShift (T : D.Niltest w) (a : ℝ) : D.Niltest w :=
  T.scaleComplex (Real.fourierChar a : ℂ)

@[simp] theorem phaseShift_orbit (T : D.Niltest w) (a : ℝ) :
    (T.phaseShift a).orbit = T.orbit := rfl

@[simp] theorem phaseShift_normBound (T : D.Niltest w) (a : ℝ) :
    (T.phaseShift a).normBound = T.normBound := by
  have hn : ‖(Real.fourierChar a : ℂ)‖₊ = 1 := by
    apply NNReal.coe_injective
    exact Circle.norm_coe _
  change ‖(Real.fourierChar a : ℂ)‖₊ * T.normBound = T.normBound
  rw [hn, one_mul]

@[simp] theorem phaseShift_lipBound (T : D.Niltest w) (a : ℝ) :
    (T.phaseShift a).lipBound = T.lipBound := by
  have hn : ‖(Real.fourierChar a : ℂ)‖₊ = 1 := by
    apply NNReal.coe_injective
    exact Circle.norm_coe _
  change ‖(Real.fourierChar a : ℂ)‖₊ * T.lipBound = T.lipBound
  rw [hn, one_mul]

@[simp] theorem phaseShift_complexity_iff (T : D.Niltest w) (a p : ℝ) :
    (T.phaseShift a).ComplexityLE p ↔ T.ComplexityLE p := by
  simp only [ComplexityLE, phaseShift_normBound, phaseShift_lipBound]

@[simp] theorem phaseShift_eval (T : D.Niltest w) (a : ℝ) (u : σ → ℤ) :
    (T.phaseShift a).eval u = (Real.fourierChar a : ℂ) * T.eval u := rfl

@[simp] theorem phaseShift_evalReal (T : D.Niltest w) (a : ℝ) (u : σ → ℝ) :
    (T.phaseShift a).evalReal u = (Real.fourierChar a : ℂ) * T.evalReal u := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalTorus

instance zeroAlgebraSubsingleton : Subsingleton (Algebra 0) :=
  inferInstanceAs (Subsingleton (Fin 0 → ℚ))

def trivialFiltration (s : ℕ) : NilpotentLieFiltration (Algebra 0) s where
  layer _ := ⊤
  antitone _ _ _ := le_rfl
  one_eq_top := rfl
  lie_mem _ _ := Submodule.mem_top
  terminal := by
    apply le_antisymm _ bot_le
    intro x _
    simpa only [Submodule.mem_bot] using (Subsingleton.elim x 0)

theorem trivialFiltration_basis_layers (s j : ℕ) :
    (trivialFiltration s).layer j = Submodule.span ℚ ((basis 0) '' {_i : Fin 0 | j ≤ (0 : ℕ)}) := by
  ext x
  rw [Subsingleton.elim x 0]
  simp only [Submodule.zero_mem]

theorem trivial_lattice_inner_grid (s : ℕ) :
    scaledIntegerGrid 1 ⊆ bchSubgroupCoordinates (basis 0) (⊤ : Subgroup (trivialFiltration s).Group) := by
  intro x _
  trivial

theorem trivial_lattice_outer_grid (s : ℕ) :
    bchSubgroupCoordinates (basis 0) (⊤ : Subgroup (trivialFiltration s).Group) ⊆ denominatorGrid 1 := by
  intro x _
  exact ⟨0, fun i => Fin.elim0 i⟩

noncomputable def trivialNilmanifold (s : ℕ) : RationalFilteredNilmanifold (Algebra 0) s 0 :=
  (trivialFiltration s).ofAdaptedBasis (basis 0) (fun _ => 0) (trivialFiltration_basis_layers s)
    ⊤ 1 (by omega) (trivial_lattice_inner_grid s) (trivial_lattice_outer_grid s)

theorem trivialNilmanifold_geometry (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (trivialNilmanifold s).GeometryComplexityLE p := by
  apply (trivialFiltration s).ofAdaptedBasis_geometry (basis 0) (fun _ => 0)
    (trivialFiltration_basis_layers s) ⊤ 1 (by omega)
    (trivial_lattice_inner_grid s) (trivial_lattice_outer_grid s) hp (by simpa using hp)
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · intro i
    exact Fin.elim0 i

theorem trivialNilmanifold_const_one_complexity (s : ℕ) {σ : Type*} (w : σ → ℕ) {p : ℝ}
    (hp : 2 ≤ p) :
    (RationalFilteredNilmanifold.Niltest.const (trivialNilmanifold s) w 1).ComplexityLE p := by
  refine ⟨trivialNilmanifold_geometry s (by linarith), ?_⟩
  change Real.log (2 + (‖(1 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ p
  simp only [nnnorm_one, NNReal.coe_one, add_zero]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at *
  linarith

end Erdos3.RationalTorus

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U : Type*}

noncomputable def zeroDegreePolynomialPhaseNiltest (w : U → ℕ)
    (P : MvPolynomial U ℝ) : (RationalTorus.trivialNilmanifold 0).Niltest w :=
  RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold 0) w
    (Real.fourierChar (P.coeff 0) : ℂ)

@[simp] theorem zeroDegreePolynomialPhaseNiltest_normBound (w : U → ℕ)
    (P : MvPolynomial U ℝ) :
    (zeroDegreePolynomialPhaseNiltest w P).normBound = 1 := by
  apply NNReal.eq
  exact Circle.norm_coe _

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

noncomputable def weightedTranslationBufferedObservable (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ) :
    (weightedTranslationNilmanifold w d hw hwd).Space → ℂ :=
  bufferedTranslationQuotientPhase Ψ D₀ ∘ weightedTranslationPhaseQuotientMap w d hw hwd

@[simp] theorem weightedTranslationBufferedObservable_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationBufferedObservable w d hw hwd Ψ D₀ (QuotientGroup.mk g) =
      bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd g) := rfl

theorem weightedTranslationBufferedObservable_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : (weightedTranslationNilmanifold w d hw hwd).Space) :
    ‖weightedTranslationBufferedObservable w d hw hwd Ψ D₀ g‖ ≤ 1 :=
  bufferedTranslationQuotientPhase_norm_le_one Ψ D₀ _

variable [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedTranslationBufferedObservable_lipschitz
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M) :
    letI := (weightedTranslationNilmanifold w d hw hwd).metricSpace
    LipschitzWith (2 * bufferedTranslationTermLip w d Ψ M)
      (weightedTranslationBufferedObservable w d hw hwd Ψ D₀) := by
  let e := (weightedOrderedBasis w d hw).baseChange ℝ
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) := e.finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace_isIsometricSMul
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  exact rightCosetMetricSpace_lipschitz_lift
    (weightedTranslationNilmanifold w d hw hwd).realLattice
    (weightedTranslationNilmanifold w d hw hwd).realLattice_closed_discrete.1
    (weightedTranslationBufferedObservable w d hw hwd Ψ D₀)
    (bufferedTranslationPhase_lipschitz w d hw hd hwd Ψ D₀ M hdegree hD)

noncomputable def weightedTranslationBufferedNiltest {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) :
    (weightedTranslationNilmanifold w d hw hwd).Niltest ω where
  orbit := q
  observable := weightedTranslationBufferedObservable w d hw hwd Ψ D₀
  normBound := 1
  lipBound := 2 * bufferedTranslationTermLip w d Ψ M
  norm_le := weightedTranslationBufferedObservable_norm_le_one w d hw hwd Ψ D₀
  lipschitz := weightedTranslationBufferedObservable_lipschitz w d hw hwd hd Ψ D₀ M hdegree hD

@[simp] theorem weightedTranslationBufferedNiltest_eval {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℤ) :
    (weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD q).eval t =
      bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω t q)) := rfl

@[simp] theorem weightedTranslationBufferedNiltest_evalReal {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℝ) :
    (weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD q).evalReal t =
      bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval ω t q)) := rfl

theorem weightedTranslationBufferedNiltest_complexity {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) {p : ℝ}
    (hgeometry : (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p)
    (hbound : Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p) :
    (weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD q).ComplexityLE p := by
  refine ⟨hgeometry, ?_⟩
  simpa only [weightedTranslationBufferedNiltest, NNReal.coe_one,
    show (2 : ℝ) + 1 = 3 by norm_num] using hbound

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

def weight : Fin 0 → ℕ := fun _ => 1

theorem weight_pos : ∀ i, 0 < weight i := fun i => Fin.elim0 i

theorem weight_le (s : ℕ) : ∀ i, weight i ≤ s := fun i => Fin.elim0 i

noncomputable local instance phaseBasisFintype (s : ℕ) :
    Fintype (WeightedBasisIndex weight s) := by
  let := weightedBasisIndex_finite weight s weight_pos
  exact Fintype.ofFinite _

noncomputable abbrev nilmanifold (s : ℕ) :=
  weightedTranslationNilmanifold weight s weight_pos (weight_le s)

noncomputable def budget (s : ℕ) : ℝ :=
  max ((0 + (0 + 1)^s + s.factorial + 2*s + 1 : ℕ) : ℝ)
    (Real.log (3 + (2 * bufferedTranslationTermLip weight s
      (localTentKernel 0 8 (by decide)) 0 : ℝ≥0)))

theorem two_le_budget (s : ℕ) : 2 ≤ budget s := by
  apply le_trans _ (le_max_left _ _)
  have hf := Nat.factorial_pos s
  have hn : 2 ≤ 0 + (0 + 1)^s + s.factorial + 2*s + 1 := by
    simp only [zero_add, one_pow]
    omega
  exact_mod_cast hn

theorem nilmanifold_geometry (s : ℕ) : (nilmanifold s).GeometryComplexityLE (budget s) := by
  apply RationalFilteredNilmanifold.GeometryComplexityLE.mono _
    (weightedTranslationNilmanifold_complexity_budget weight s weight_pos (weight_le s))
  simpa only [Fintype.card_fin, budget] using le_max_left
    (((0 + (0 + 1)^s + s.factorial + 2*s + 1 : ℕ) : ℝ))
    (Real.log (3 + (2 * bufferedTranslationTermLip weight s
      (localTentKernel 0 8 (by decide)) 0 : ℝ≥0)))

theorem specialize_rename {U : Type*} (P : MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) (rename (Sum.inl : U → U ⊕ Fin 0) P) u =
      C (eval u P) := by
  simp only [specializeMajorParameters, RingHom.comp_id, eval₂Hom_rename]
  change eval₂ C (fun i => C (u i)) P = C (eval u P)
  exact (eval₂_comp C u P).symm

theorem exists_phase_orbit {U : Type*} (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    ∃ q : (nilmanifold s).filtration.realification.PolynomialOrbit (fun _ : U => 1),
      ∀ u : U → ℝ,
        bchRealTranslationHom weight s (weight_le s)
          ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
            (fun _ : U => 1) u q) = ⟨0, C (eval u P)⟩ := by
  have hslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) (rename (Sum.inl : U → U ⊕ Fin 0) P) u ∈
        weightedSupportLT weight s := by
    intro u α _
    have hα : α = 0 := Subsingleton.elim _ _
    change Finsupp.weight weight α < s
    simpa only [hα, map_zero] using hs
  obtain ⟨q, hq⟩ := exists_translation_coordinate_polynomialOrbit weight s weight_pos
    (weight_le s) (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i)
    (rename Sum.inl P)
    (majorParameterRename_degree (fun _ : U => 1) weight
      ((mem_weightedSupportLE_one_iff P s).mpr hP)) hslot
  refine ⟨q, fun u => ?_⟩
  change bchRealTranslationHom weight s (weight_le s)
    ((weightedFiltration weight s (weight_le s)).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u q) = _
  rw [hq u, specialize_rename]
  rfl

variable {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s)]

theorem exists_niltest {U : Type*} (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    ∃ T : (nilmanifold s).Niltest (fun _ : U => 1),
      T.normBound = 1 ∧ T.ComplexityLE (budget s) ∧
      ∀ u : U → ℝ, T.evalReal u = (Real.fourierChar (eval u P) : ℂ) := by
  obtain ⟨q, hq⟩ := exists_phase_orbit s hs P hP
  let Ψ := localTentKernel 0 8 (by decide)
  let T := weightedTranslationBufferedNiltest weight s weight_pos (weight_le s)
    (fun _ : U => 1) hs Ψ 0 0 (by simp) (by simp [realPolynomialMass]) q
  refine ⟨T, rfl, ?_, ?_⟩
  · apply weightedTranslationBufferedNiltest_complexity
    · exact nilmanifold_geometry s
    · exact le_max_right _ _
  · intro u
    change bufferedTranslationPhase Ψ 0 (bchRealTranslationHom weight s (weight_le s)
      ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
        (fun _ : U => 1) u q)) = _
    rw [hq u]
    rw [bufferedTranslationPhase_eq_chart Ψ 0 _ 0 (fun i => Fin.elim0 i)]
    have hd : ∀ x y : Fin 0 → ℝ, dist x y = 0 := by
      intro x y
      rw [Subsingleton.elim x y, dist_self]
    simp [bufferedTranslationTerm, translationPhaseArgument, Ψ, localTentKernel, hd]

theorem exists_niltest_of_degree {U : Type*}
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    ∃ T : (nilmanifold s).Niltest (fun _ : U => 1),
      T.normBound = 1 ∧ T.ComplexityLE (budget s) ∧
      ∀ u : U → ℝ, T.evalReal u = (Real.fourierChar (eval u P) : ℂ) := by
  by_cases hs : 0 < s
  · exact exists_niltest hs P hP
  · have hs : s = 0 := by omega
    subst s
    let T := RationalFilteredNilmanifold.Niltest.const (nilmanifold 0)
      (fun _ : U => 1) (Real.fourierChar (P.coeff 0) : ℂ)
    have hn : T.normBound = 1 := by
      apply NNReal.eq
      exact Circle.norm_coe _
    refine ⟨T, hn, ⟨nilmanifold_geometry 0, ?_⟩, ?_⟩
    · rw [hn]
      change Real.log (2 + (1 : ℝ) + 0) ≤ budget 0
      have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      norm_num at hl ⊢
      exact hl.trans (two_le_budget 0)
    · intro u
      have heq : P = C (P.coeff 0) :=
        totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hP)
      change (Real.fourierChar (P.coeff 0) : ℂ) = (Real.fourierChar (eval u P) : ℂ)
      conv_rhs => rw [heq, eval_C]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

theorem exists_localMajor_slice_niltest
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let K := ((n + 1 : ℕ) + 1 : ℝ) * ((Fintype.card U : ℝ) + 1) ^ (n + 1) *
      M * Fintype.card U * (n + 1)
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * (q : ℝ) ≤ ρ * N i) →
    ∃ A : ResidueBoxSlice N q,
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i) ∧
      (𝔼 x, f x) ≤ (𝔼 j : (∀ i, Fin (A.length i)), f (A.point j)) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        1 - 2 * Real.pi * δ ≤ ‖𝔼 j : (∀ i, Fin (A.length i)),
          (Real.fourierChar (eval (fun i => ((A.point j i).val : ℝ)) P) : ℂ) *
            star (T.eval (fun i => ((j i).val : ℤ)))‖ := by
  intro K ρ hlarge
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hKρ : K * ρ ≤ δ := by
    have hle := (le_div_iff₀ (by linarith : 0 < K + 1)).mp
      (min_le_right (1 : ℝ) (δ / (K + 1)))
    change ρ * (K + 1) ≤ δ at hle
    nlinarith
  obtain ⟨A, hA, hscore, hslow⟩ := exists_slowPolynomial_residueSlice N hq hρ
    (min_le_left _ _) hM hlarge E hE hcoeff f
  let r : U → ℤ := fun i => (A.start i : ℤ)
  let v : (∀ i, Fin (A.length i)) → U → ℤ := fun j i => ((j i).val : ℤ)
  let Q := localMajorLowerPhase n q r P
  obtain ⟨T, hnorm, hbudget, hT⟩ := OrdinaryPolynomialPhase.exists_niltest_of_degree
    Q (localMajorLowerPhase_totalDegree_le n q r P hP)
  refine ⟨A, hA, hscore, T, hnorm, hbudget, ?_⟩
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, (hA i).1⟩⟩
  have hpoint (j : ∀ i, Fin (A.length i)) :
      (fun i => ((r i + (q : ℤ) * v j i : ℤ) : ℝ)) =
        (fun i => ((A.point j i).val : ℝ)) := by
    funext i
    simp only [r, v, ResidueBoxSlice.point, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Nat.cast_add, Nat.cast_mul]
  have hlocal := (localMajorPhaseCorrelation
    (FiniteProbabilityWeights.uniform (∀ i, Fin (A.length i))) v n q hq r P E R hP htop hR
    (eval (fun i => (A.start i : ℝ)) E) δ (by
      intro j _
      rw [hpoint j]
      exact (hslow j).trans (by simpa only [K, Nat.cast_add, Nat.cast_one] using hKρ))).2
  rw [FiniteProbabilityWeights.uniform_complexMean] at hlocal
  have heval (j : ∀ i, Fin (A.length i)) : T.eval (v j) =
      (Real.fourierChar (eval (fun i => (v j i : ℝ)) Q) : ℂ) := by
    rw [← T.evalReal_integer, hT]
  simpa only [hpoint, heval, Q, v] using hlocal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

theorem exists_localMajor_dense_slice_niltest
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (U → ℤ) → ℝ) :
    let K := ((n + 1 : ℕ) + 1 : ℝ) * ((Fintype.card U : ℝ) + 1) ^ (n + 1) *
      M * Fintype.card U * (n + 1)
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * (q : ℝ) ≤ ρ * N i) →
    ∃ A : ResidueBoxSlice N q,
      IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints ∧
      (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ A.integerPoints, f x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        1 - 2 * Real.pi * δ ≤ ‖𝔼 x ∈ A.integerPoints,
          (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) *
            star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  intro K ρ hlarge
  obtain ⟨A, hA, hscore, T, hnorm, hbudget, hcorr⟩ := exists_localMajor_slice_niltest
    N q hq P E R hP hE htop hR M δ hM hδ hcoeff
    (fun x => f (fun i => ((x i).val : ℤ))) hlarge
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hδ (by linarith))
  refine ⟨A, A.isDenseCommonStrideBox hq hρ (fun i => (hA i).1)
    (fun i => (hA i).2), ?_, T, hnorm, hbudget, ?_⟩
  · rw [A.expect_integerPoints hq]
    exact hscore
  · rw [A.expect_integerPoints hq]
    simp only [A.commonStrideIndex_integerPoint hq, ResidueBoxSlice.integerPoint,
      Int.cast_natCast]
    exact hcorr

theorem major_phase_nine_tenths :
    1 - 2 * Real.pi * (1 / (20 * Real.pi)) = (9 / 10 : ℝ) := by
  field_simp
  ring

theorem exists_localMajor_dense_slice_niltest_nine_tenths
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (U → ℤ) → ℝ) :
    let K := ((n + 1 : ℕ) + 1 : ℝ) * ((Fintype.card U : ℝ) + 1) ^ (n + 1) *
      M * Fintype.card U * (n + 1)
    let ρ := min 1 ((1 / (20 * Real.pi)) / (K + 1))
    (∀ i, 4 * (q : ℝ) ≤ ρ * N i) →
    ∃ A : ResidueBoxSlice N q,
      IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints ∧
      (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ A.integerPoints, f x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
          (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) *
            star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  simpa only [major_phase_nine_tenths] using exists_localMajor_dense_slice_niltest
    N q hq P E R hP hE htop hR M (1 / (20 * Real.pi)) hM (by positivity) hcoeff f

theorem exists_localMajor_dense_slice_niltest_early
    (N : U → ℕ) (q : ℕ) (hq : 0 < q)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (hE : E.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R)
    (M p : ℝ) (hM : 0 ≤ M) (hp : 1 ≤ p)
    (hdim : (Fintype.card U : ℝ) ≤ p) (hMexp : M ≤ Real.exp p)
    (hqexp : (q : ℝ) ≤ Real.exp p)
    (hcoeff : ∀ α, |E.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (U → ℤ) → ℝ)
    (hN : ∀ i, Real.exp ((p + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) :
    ∃ A : ResidueBoxSlice N q,
      IsDenseCommonStrideBox N ((p + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
      (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
        (𝔼 x ∈ A.integerPoints, f x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
          (Real.fourierChar (eval (fun i => (x i : ℝ)) P) : ℂ) *
            star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  let ρ := slowPolynomialSliceRadius (n + 1) (Fintype.card U) M
  have hρ : 0 < ρ := slowPolynomialSliceRadius_pos _ _ hM
  have hcost : Real.log (4 * (q : ℝ) / ρ) ≤ (p + (n + 401 : ℕ)) ^ (n + 401) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using slowPolynomialSlice_log_cost
      (n + 1) (Fintype.card U) hp hdim hM hMexp (by exact_mod_cast hq) hqexp
  have hlarge : ∀ i, 4 * (q : ℝ) ≤ ρ * N i := by
    intro i
    have hratio : 4 * (q : ℝ) / ρ ≤ Real.exp ((p + (n + 401 : ℕ)) ^ (n + 401)) :=
      (Real.log_le_iff_le_exp (by positivity)).mp hcost
    simpa only [mul_comm] using (div_le_iff₀ hρ).mp (hratio.trans (hN i))
  obtain ⟨A, hA, hscore, hT⟩ := exists_localMajor_dense_slice_niltest_nine_tenths
    N q hq P E R hP hE htop hR M hM hcoeff f (by
      simpa only [ρ, slowPolynomialSliceRadius, slowPolynomialSliceSlope,
        Nat.cast_add, Nat.cast_one] using hlarge)
  have hA' : IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints := by
    simpa only [ρ, slowPolynomialSliceRadius, slowPolynomialSliceSlope,
      Nat.cast_add, Nat.cast_one] using hA
  exact ⟨A, hA'.mono hcost, hscore, hT⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedTranslationBufferedCentralFrequency
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def centralConstantPolynomial (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (t : ℝ) : weightedSupportLT (R := ℝ) w d :=
  ⟨C t, (monomial_mem_restrictSupport ℝ).mpr (Or.inl (by simpa using hd))⟩

noncomputable def centralRealLine (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    (weightedFiltration w d hwd).realification.Group :=
  ⟨polynomialRealElement w d hw (centralConstantPolynomial w d hd t)⟩

@[simp] theorem centralRealLine_map (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    bchRealTranslationHom w d hwd (centralRealLine w d hw hd hwd t) = ⟨0, C t⟩ :=
  bchRealTranslationHom_pure_polynomial_of_shape w d hwd _ _
    (polynomialRealElement_shear_base w d hw _)
    (polynomialRealElement_shear_extra w d hw _)

@[simp] theorem centralRealLine_zero (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) :
    centralRealLine w d hw hd hwd 0 = 1 := by
  apply bchRealTranslationHom_injective w d hwd
  simp only [centralRealLine_map, map_one, map_zero]
  rfl

@[simp] theorem centralRealLine_add (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t u : ℝ) :
    centralRealLine w d hw hd hwd (t + u) =
      centralRealLine w d hw hd hwd t * centralRealLine w d hw hd hwd u := by
  apply bchRealTranslationHom_injective w d hwd
  simp only [map_mul, centralRealLine_map]
  apply PolynomialTranslationGroupOver.ext <;> simp

 theorem centralRealLine_commute (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    Commute (centralRealLine w d hw hd hwd t) g := by
  apply bchRealTranslationHom_injective w d hwd
  simp only [map_mul, centralRealLine_map]
  apply PolynomialTranslationGroupOver.ext <;> simp [add_comm]

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationBufferedObservable_central
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (t : ℝ)
    (q : (weightedTranslationNilmanifold w d hw hwd).Space) :
    weightedTranslationBufferedObservable w d hw hwd Ψ D₀
      (centralRealLine w d hw hd hwd t • q) =
    weightedTranslationBufferedObservable w d hw hwd Ψ D₀ q *
      (Real.fourierChar t : ℂ) := by
  induction q using Quotient.inductionOn with
  | h g =>
    change weightedTranslationBufferedObservable w d hw hwd Ψ D₀
      (QuotientGroup.mk (centralRealLine w d hw hd hwd t * g)) = _
    rw [(centralRealLine_commute w d hw hd hwd t g).eq]
    simp only [weightedTranslationBufferedObservable_mk, map_mul, centralRealLine_map]
    exact bufferedTranslationPhase_central Ψ D₀ _ t

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationCentralTop
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

@[simp] theorem centralRealLine_coord (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    (centralRealLine w d hw hd hwd t).coord =
      t ⊗ₜ[ℚ] centralRationalElement w d hd 1 := by
  classical
  apply ((weightedBasis w d hw).baseChange ℝ).repr.injective
  ext a
  change ((weightedBasis w d hw).baseChange ℝ).repr
    (polynomialRealElement w d hw (centralConstantPolynomial w d hd t)) a = _
  rw [polynomialRealElement_repr, Basis.baseChange_repr_tmul]
  cases a with
  | inl i => simp [weightedBasis_repr_inl, centralRationalElement]
  | inr a =>
    simp only [Sum.elim_inr, centralConstantPolynomial, weightedBasis_repr_inr,
      centralRationalElement, coeff_C]
    split_ifs <;> simp

 theorem centralRationalElement_mem_top (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) (q : ℚ) :
    centralRationalElement w d hd q ∈ (weightedFiltration w d hwd).layer d := by
  refine ⟨fun i hi => rfl, ?_⟩
  exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationTwistedNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

noncomputable def weightedTranslationTwistedObservable (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space → ℂ :=
  twistedBufferedTranslationQuotientPhase M Ψ D₀ T ∘
    weightedTranslationResiduePhaseQuotientMap w d hw hwd M hM

@[simp] theorem weightedTranslationTwistedObservable_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T (QuotientGroup.mk g) =
      twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd g) := rfl

theorem weightedTranslationTwistedObservable_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space) :
    ‖weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T g‖ ≤ 1 :=
  twistedBufferedTranslationQuotientPhase_norm_le_one M Ψ D₀ T hT _

variable [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedTranslationTwistedObservable_lipschitz
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r)) :
    letI := (weightedTranslationResidueNilmanifold w d hw hwd M hM).metricSpace
    LipschitzWith (2 * twistedBufferedTranslationTermLip w d Ψ A K)
      (weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T) := by
  let e := (weightedOrderedBasis w d hw).baseChange ℝ
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) := e.finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace_isIsometricSMul
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  exact rightCosetMetricSpace_lipschitz_lift
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice_closed_discrete.1
    (weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T)
    (twistedBufferedTranslationPhase_lipschitz w d hw hd hwd M Ψ D₀ A K hdegree hD T hT hLip)

noncomputable def weightedTranslationTwistedNiltest {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest ω where
  orbit := q
  observable := weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T
  normBound := 1
  lipBound := 2 * twistedBufferedTranslationTermLip w d Ψ A K
  norm_le := weightedTranslationTwistedObservable_norm_le_one w d hw hwd M hM Ψ D₀ T hT
  lipschitz := weightedTranslationTwistedObservable_lipschitz
    w d hw hwd M hM hd Ψ D₀ A K hdegree hD T hT hLip

@[simp] theorem weightedTranslationTwistedNiltest_eval {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℤ) :
    (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD T hT hLip q).eval t =
      twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω t q)) := rfl

@[simp] theorem weightedTranslationTwistedNiltest_evalReal {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℝ) :
    (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD T hT hLip q).evalReal t =
      twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval ω t q)) := rfl

theorem weightedTranslationTwistedNiltest_complexity {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) {p : ℝ}
    (hgeometry : (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p)
    (hbound : Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0)) ≤ p) :
    (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD T hT hLip q).ComplexityLE p := by
  refine ⟨hgeometry, ?_⟩
  simpa only [weightedTranslationTwistedNiltest, NNReal.coe_one,
    show (2 : ℝ) + 1 = 3 by norm_num] using hbound

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem detector_of_unit_detector {X : Type*} [Fintype X]
    (μ : FiniteProbabilityWeights X) (S : Seminorm ℂ (X → ℂ)) (atoms : Set (X → ℂ))
    {R δ β : ℝ} (hR : 0 < R)
    (hdetect : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) → δ / R ≤ S g →
      ∃ Q ∈ atoms, β ≤ ‖μ.correlation g Q‖)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ R) (hS : δ ≤ S f) :
    ∃ Q ∈ atoms, R * β ≤ ‖μ.correlation f Q‖ := by
  let g : X → ℂ := (R : ℂ)⁻¹ • f
  have hg (x : X) : ‖g x‖ ≤ 1 := by
    change ‖(R : ℂ)⁻¹ * f x‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    calc
      R⁻¹ * ‖f x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hf x) (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have hSg : δ / R ≤ S g := by
    dsimp only [g]
    rw [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hR.le)
  obtain ⟨Q, hQ, hcorr⟩ := hdetect g hg hSg
  have heq : μ.correlation g Q = (R : ℂ)⁻¹ * μ.correlation f Q := by
    simp only [FiniteProbabilityWeights.correlation, g, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le] at hcorr
  refine ⟨Q, hQ, ?_⟩
  have h := mul_le_mul_of_nonneg_left hcorr hR.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] using h

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeSampleCorrelation {σ X : Type*} (w : σ → ℕ)
    (degree : ℕ) (p : ℝ) (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  complexity : test.ComplexityLE p
  correlation : Real.exp (-p) ≤ ‖𝔼 x ∈ S, f x * star (test.eval (sample x))‖

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeSampleCorrelation

variable {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
  {S : Finset X} {sample : X → σ → ℤ} {f : X → ℂ}

noncomputable def mono (V : NativeSampleCorrelation w s p S sample f) (hpq : p ≤ q) :
    NativeSampleCorrelation w s q S sample f :=
  { V with
    complexity := V.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans V.correlation }

theorem exists_of_expansion {eta : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p eta) (hq : 0 ≤ q)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 x ∈ S, f x * star (eta (sample x))‖) :
    Nonempty (NativeSampleCorrelation w s (q + p) S sample f) := by
  obtain ⟨i, hi⟩ := E.select_sample_correlation S sample f hcorr
  exact ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono (le_add_of_nonneg_left hq)
    correlation := hi }⟩

end NativeSampleCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct Pointwise BigOperators

structure NativeSampleModel {σ X : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (f : X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  norm : test.normBound ≤ 1
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = test.eval (sample x)

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

noncomputable def NativeSampleModel.constOne (hp : 2 ≤ p) :
    NativeSampleModel w degree p sample (fun _ => 1) where
  L := RationalTorus.Algebra 0
  dim := 0
  model := RationalTorus.trivialNilmanifold degree
  test := RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold degree) w 1
  norm := by simp [RationalFilteredNilmanifold.Niltest.const]
  complexity := RationalTorus.trivialNilmanifold_const_one_complexity degree w hp
  eval _ := rfl

noncomputable def NativeSampleCorrelation.ofMean {S : Finset X} (hp : 2 ≤ p)
    (hmean : Real.exp (-p) ≤ ‖𝔼 x ∈ S, f x‖) :
    NativeSampleCorrelation w degree p S sample f where
  L := RationalTorus.Algebra 0
  dim := 0
  model := RationalTorus.trivialNilmanifold degree
  test := RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold degree) w 1
  complexity := RationalTorus.trivialNilmanifold_const_one_complexity degree w hp
  correlation := by simpa only [RationalFilteredNilmanifold.Niltest.eval_const, star_one, mul_one] using hmean

noncomputable def NativeSampleModel.smul (F : NativeSampleModel w degree p sample f)
    (c : ℂ) (hc : ‖c‖ ≤ 1) : NativeSampleModel w degree p sample (c • f) where
  L := F.L
  dim := F.dim
  model := F.model
  test := F.test.scaleComplex c
  norm := (F.test.scaleComplex_norm hc).trans F.norm
  complexity := F.test.scaleComplex_complexity hc F.complexity
  eval x := by change c * f x = c * F.test.eval (sample x); rw [F.eval]

theorem NativeSampleModel.norm_le (F : NativeSampleModel w degree p sample f) (x : X) :
    ‖f x‖ ≤ 1 := by
  rw [F.eval]
  exact (F.test.norm_eval_le _).trans F.norm

def twistedNativeSampleFunctions {I : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (twist : I → X → ℂ) : Set (X → ℂ) :=
  {f | f = 0 ∨ ∃ i g, Nonempty (NativeSampleModel w degree p sample g) ∧
    f = fun x => star (twist i x) * g x}

theorem twistedNativeSampleFunctions_zero {I : Type*} (twist : I → X → ℂ) :
    (0 : X → ℂ) ∈ twistedNativeSampleFunctions w degree p sample twist := Or.inl rfl

theorem twistedNativeSampleFunctions_balanced {I : Type*} (twist : I → X → ℂ) :
    Balanced ℂ (twistedNativeSampleFunctions w degree p sample twist) := by
  rintro c hc _ ⟨f, hf, rfl⟩
  rcases hf with rfl | ⟨i, g, ⟨G⟩, rfl⟩
  · exact Or.inl (smul_zero c)
  · refine Or.inr ⟨i, c • g, ⟨G.smul c hc⟩, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem twistedNativeSampleFunctions_norm {I : Type*} (twist : I → X → ℂ)
    (htwist : ∀ i x, ‖twist i x‖ ≤ 1)
    (hf : f ∈ twistedNativeSampleFunctions w degree p sample twist) (x : X) : ‖f x‖ ≤ 1 := by
  rcases hf with rfl | ⟨i, g, ⟨G⟩, rfl⟩
  · simp
  · rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (htwist i x)).trans (G.norm_le x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold.Niltest

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {degree dim : ℕ}
  {D : RationalFilteredNilmanifold L degree dim}

noncomputable def commonStridePullback (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) : D.Niltest (fun _ : I => 1) :=
  T.affinePullback (residueStepMatrix (fun _ : I => m)) c

@[simp] theorem commonStridePullback_observable (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) :
    (T.commonStridePullback c m).observable = T.observable := rfl

@[simp] theorem commonStridePullback_normBound (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) :
    (T.commonStridePullback c m).normBound = T.normBound := rfl

@[simp] theorem commonStridePullback_lipBound (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) :
    (T.commonStridePullback c m).lipBound = T.lipBound := rfl

@[simp] theorem commonStridePullback_complexityLE (T : D.Niltest (fun _ : I => 1))
    (c : I → ℤ) (m : ℕ) (p : ℝ) :
    (T.commonStridePullback c m).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end RationalFilteredNilmanifold.Niltest

namespace RationalFilteredNilmanifold.Niltest

variable {I Ω : Type*} {L : Type} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {degree dim : ℕ}
  {D : RationalFilteredNilmanifold L degree dim} {p : ℝ}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

structure VerticalExpansion (native : NativeSampleModel w degree p sample f)
    (q rho : ℝ) where
  I : Type
  [finite : Fintype I]
  frequency : I → native.L →ₗ[ℚ] ℚ
  component : I → native.model.Niltest w
  card_le : (Fintype.card I : ℝ) ≤ Real.exp (verticalDecompositionBudget q)
  height_le : ∀ i j, rationalLogHeight (frequency i (native.model.basis j)) ≤
    verticalDecompositionBudget q
  orbit_eq : ∀ i, (component i).orbit = native.test.orbit
  norm_eq : ∀ i, (component i).normBound = native.test.normBound
  lip_eq : ∀ i, (component i).lipBound = native.test.lipBound
  vertical : ∀ i (z : native.model.RealGroup),
    z ∈ native.model.filtration.realification.subgroup degree → ∀ x,
      (component i).observable (z • x) =
        character ((realifyFunctional (frequency i) z.coord : ℝ) : CircleFourier.Circle) *
          (component i).observable x
  integral : ∀ i, (∃ x, (component i).observable x ≠ 0) →
    ∀ z : native.model.RealGroup,
      z ∈ native.model.filtration.realification.subgroup degree →
      z ∈ native.model.realLattice → ∃ n : ℤ, realifyFunctional (frequency i) z.coord = n
  preserves_character : ∀ (z : native.model.RealGroup) (c : ℂ),
    (∀ x, native.test.observable (z • x) = c * native.test.observable x) →
      ∀ i x, (component i).observable (z • x) = c * (component i).observable x
  observable_error : ∀ x,
    ‖(∑ i, (component i).observable x) - native.test.observable x‖ ≤ rho

attribute [instance] VerticalExpansion.finite

namespace VerticalExpansion

variable {native : NativeSampleModel w degree p sample f} {q rho : ℝ}
  (E : native.VerticalExpansion q rho)

theorem complexity (i : E.I) : (E.component i).ComplexityLE p := by
  refine ⟨native.complexity.1, ?_⟩
  rw [E.norm_eq, E.lip_eq]
  exact native.complexity.2

end VerticalExpansion
end Erdos3.NativeSampleModel

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_sampled_native_model {Ω T X σ I : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (slices : ∀ z, J z → Finset T) (tests : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    (w : σ → ℕ) (degree : ℕ) (complexity : ℝ) (sample : X → σ → ℤ)
    (twist : I → X → ℂ) (htwist : ∀ i x, ‖twist i x‖ ≤ 1)
    {K C B beta tau ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      (tau / B ^ 2) / max 1 (K * (2 * C) / tau) ≤ sampledSliceSeminorm μ F slices tests g →
      ∃ (i : I) (G : X → ℂ), Nonempty (NativeSampleModel w degree complexity sample G) ∧
        beta ≤ ‖r.correlation g (fun x => star (twist i x) * G x)‖)
    (hexcess : r.excessMass (μ.siteLaw F) C ≤ ε)
    (b : X → ℂ) (hb : ∀ x, ‖b x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (e : X → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree complexity sample twist) ∧
      b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ F slices tests e ≤ 2 * tau + 2 * K * (B + 2 / beta) * ε ∧
      (n : ℝ) ≤ 1 + 4 * (K * (2 * C)) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let atoms := twistedNativeSampleFunctions w degree complexity sample twist
  let cap := max 1 (K * (2 * C) / tau)
  have hcap : 1 ≤ cap := le_max_left _ _
  have hdetector (g : X → ℂ) (hg : ∀ x, ‖g x‖ ≤ K * (2 * C) / tau)
      (hlarge : tau / B ^ 2 ≤ sampledSliceSeminorm μ F slices tests g) :
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
    have hunit (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
        (hX : (tau / B ^ 2) / cap ≤ sampledSliceSeminorm μ F slices tests v) :
        ∃ Q ∈ atoms, beta ≤ ‖r.correlation v Q‖ := by
      obtain ⟨i, G, hG, hcorr⟩ := hdetect v hv hX
      exact ⟨_, Or.inr ⟨i, G, hG, rfl⟩, hcorr⟩
    obtain ⟨Q, hQ, hc⟩ := detector_of_unit_detector r
      (sampledSliceSeminorm μ F slices tests) atoms (lt_of_lt_of_le zero_lt_one hcap)
      hunit g (fun x => (hg x).trans (le_max_right _ _)) hlarge
    have hscale : beta ≤ cap * beta := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcap hbeta.le
    exact ⟨Q, hQ, hscale.trans hc⟩
  exact exists_sampled_slice_model μ F slices tests r hr
    (twistedNativeSampleFunctions_balanced twist) ⟨0, twistedNativeSampleFunctions_zero twist⟩
    (fun Q hQ x => twistedNativeSampleFunctions_norm twist htwist hQ x)
    hK hC hB hbeta htau hsize htests hdetector hexcess b hb

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExternalPhysicalMemberPivotMasks
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {L σ I : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d)

noncomputable def externalNetNiltest (f : D.Space → ℂ) (K : ℝ≥0)
    (hcap : ∀ x, ‖f x‖ ≤ 1) (hLip : letI := D.metricSpace; LipschitzWith K f)
    {w : σ → ℕ} (orbit : D.filtration.realification.PolynomialOrbit w) : D.Niltest w where
  orbit := orbit
  observable := f
  normBound := 1
  lipBound := K
  norm_le := hcap
  lipschitz := hLip

theorem externalNetNiltest_complexity
    (f : D.Space → ℂ) (K : ℝ≥0)
    (hcap : ∀ x, ‖f x‖ ≤ 1) (hLip : letI := D.metricSpace; LipschitzWith K f)
    {w : σ → ℕ} (orbit : D.filtration.realification.PolynomialOrbit w)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hK : (K : ℝ) ≤ Real.exp p) :
    (D.externalNetNiltest f K hcap hLip orbit).ComplexityLE (p + 3) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + (K : ℝ)) ≤ p + 3
  apply (Real.log_le_iff_le_exp (by positivity)).2
  have he : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have hthree : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    2 + 1 + (K : ℝ) ≤ 4 * Real.exp p := by linarith
    _ ≤ Real.exp 3 * Real.exp p := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg p)
    _ = Real.exp (p + 3) := by rw [← Real.exp_add, add_comm]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_uniform_controlled_vertical_operators {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (δ : ℝ) (hδ : 0 < δ) (hδp : δ⁻¹ ≤ Real.exp p) :
    letI := D.metricSpace
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (η : J → L →ₗ[ℚ] ℚ) (V : J → (D.Space → ℂ) → D.Space → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j (f g : D.Space → ℂ) (K H : ℝ≥0), LipschitzWith K f → LipschitzWith H g →
        ∀ ε : ℝ, (∀ x, ‖f x - g x‖ ≤ ε) → ∀ x, ‖V j f x - V j g x‖ ≤ ε) ∧
      ∀ (f : D.Space → ℂ) (K B : ℝ≥0), LipschitzWith K f → (∀ x, ‖f x‖ ≤ B) →
        (K : ℝ) ≤ Real.exp p →
        (∀ j, LipschitzWith K (V j f) ∧ (∀ x, ‖V j f x‖ ≤ B)) ∧
        (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          V j f (z • x) = character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * V j f x) ∧
        (∀ (z : D.RealGroup) (c : ℂ), (∀ x, f (z • x) = c * f x) →
          ∀ j x, V j f (z • x) = c * V j f x) ∧
        ∀ x, ‖(∑ j, V j f x) - f x‖ ≤ δ := by
  classical
  let := D.metricSpace
  obtain ⟨b, w, N, hlayers, _, hbinv, hN, hNp, _, _, A, hcomm, horbit, hact⟩ :=
    D.exists_controlled_central_actions hp hD
  let S : Set (Fin (finrank ℚ L)) := {j | s ≤ w j}
  let q := centralActionBudget p
  have hq : 0 ≤ q := centralActionBudget_nonneg hp
  have hpq : p ≤ q := le_centralActionBudget hp
  have hd : (Fintype.card S : ℝ) ≤ p := by
    apply (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hD.1
  let O : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos q).le⟩
  obtain ⟨J, inst, ν, V, hcard, hν, hcontract, hdecomp⟩ :=
    exists_uniform_controlled_commuting_circle_operators A hcomm O horbit δ q hδ hq
      (hd.trans hpq) le_rfl (hδp.trans (Real.exp_le_exp.mpr hpq))
  let η : J → L →ₗ[ℚ] ℚ := fun j => basisFrequency b S N (ν j)
  let R : ℝ := (2 * q + 2) ^ 4 + q + (p + 3) ^ 5
  have hpow : 0 ≤ (p + 3) ^ 5 := by positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hqR : q ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hfreq : (2 * q + 2) ^ 4 ≤ R := by dsimp [R]; linarith
  have hbas : (p + 3) ^ 5 ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hNq : (p + 3) ^ 9 ≤ q := by dsimp [q, centralActionBudget]; linarith
  have hterm : 2 * q * (2 * q + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ _ + (R + 2) ^ 4
    exact le_add_of_nonneg_right (by positivity)
  have hheight : (R + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ 2 * q * (2 * q + 2) ^ 4 + _
    have h : 0 ≤ 2 * q * (2 * q + 2) ^ 4 := by positivity
    linarith
  have hcentral (i : S) (z : L) : ⁅b i, z⁆ = 0 := by
    apply D.filtration.top_layer_central
    rw [hlayers s]
    exact Submodule.subset_span ⟨i, i.property, rfl⟩
  have hucentral (i : S) (z : ℝ ⊗[ℚ] L) : ⁅(N : ℝ) • b.baseChange ℝ i, z⁆ = 0 :=
    scaled_real_basis_central b i (hcentral i) N z
  refine ⟨J, inst, η, V, hcard.trans (Real.exp_le_exp.mpr hterm), ?_, hcontract, ?_⟩
  · intro j i
    exact (basisFrequency_logHeight_le D.basis b S N hN (ν j) hR (hd.trans (hpq.trans hqR))
      (hNp.trans (Real.exp_le_exp.mpr (hNq.trans hqR)))
      (fun a => (hν j a).trans (Real.exp_le_exp.mpr hfreq))
      (fun a c => (hbinv a c).trans hbas) i).trans hheight
  · intro f K B hf hb hK
    obtain ⟨hv, hchar, hpres, herr⟩ :=
      hdecomp f K B hf hb (hK.trans (Real.exp_le_exp.mpr hpq))
    refine ⟨hv, ?_, ?_, herr⟩
    · intro j z hz x
      apply central_span_character (fun i : S => (N : ℝ) • b.baseChange ℝ i) hucentral
        (realifyFunctional (η j)) (V j f) ?_ ?_ x
      · intro i r y
        have h := hchar j i (r : CircleFourier.Circle) y
        rw [hact] at h
        change _ = character ((r * realifyFunctional (basisFrequency b S N (ν j))
          ((N : ℝ) • b.baseChange ℝ i) : ℝ) : CircleFourier.Circle) * _
        rw [realify_basisFrequency_direction b S N hN (ν j) i]
        simpa only [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm] using h
      · exact D.filtration.realLayer_le_span_scaled_basis b s S (hlayers s) N hN hz
    · intro z c hc
      apply hpres (fun x => z • x) c ?_ hc
      intro i t x
      obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
      rw [hact, hact, ← mul_smul, ← mul_smul]
      rw [(realBCHLine_commute _ (hucentral i) r z).eq]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {L σ I X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem contractiveFamily_integer_error {J : Type*} [Fintype J]
    (T : X → D.Niltest w) (U : J → X → D.Niltest w)
    (hU : ∀ j a, (U j a).orbit = (T a).orbit) (δ : ℝ)
    (herr : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) :
    ∀ a (x : σ → ℤ), ‖(T a).eval x - ∑ j, (U j a).eval x‖ ≤ δ := by
  intro a x
  simpa only [Niltest.eval, hU] using
    herr a (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x (T a).orbit))

theorem contractiveFamily_real_error {J : Type*} [Fintype J]
    (T : X → D.Niltest w) (U : J → X → D.Niltest w)
    (hU : ∀ j a, (U j a).orbit = (T a).orbit) (δ : ℝ)
    (herr : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) :
    ∀ a (x : σ → ℝ), ‖(T a).evalReal x - ∑ j, (U j a).evalReal x‖ ≤ δ := by
  intro a x
  simpa only [Niltest.evalReal, hU] using
    herr a (QuotientGroup.mk (D.filtration.realification.polynomialOrbitRealEval w x (T a).orbit))

theorem exists_externalFamily_contractive_vertical_expansion {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (T : X → D.Niltest w)
    (hT : ∀ a, (T a).ComplexityLE p) (δ : ℝ) (hδ : 0 < δ)
    (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j a, (U j a).ComplexityLE p ∧ (U j a).orbit = (T a).orbit ∧
        (U j a).normBound = (T a).normBound ∧ (U j a).lipBound = (T a).lipBound) ∧
      (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j a).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
            (U j a).observable x) ∧
      (∀ j a, (∃ x, (U j a).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (eta j) z.coord = n) ∧
      (∀ a (z : D.RealGroup) (c : ℂ),
        (∀ x, (T a).observable (z • x) = c * (T a).observable x) →
          ∀ j x, (U j a).observable (z • x) = c * (U j a).observable x) ∧
      (∀ j a b (ε : ℝ), (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
        ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε) ∧
      (∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) ∧
      (∀ a (x : σ → ℤ), ‖(T a).eval x - ∑ j, (U j a).eval x‖ ≤ δ) ∧
      ∀ a (x : σ → ℝ), ‖(T a).evalReal x - ∑ j, (U j a).evalReal x‖ ≤ δ := by
  classical
  let := D.metricSpace
  obtain ⟨J, inst, eta, V, hcard, hheight, hcontract, hdecomp⟩ :=
    D.exists_uniform_controlled_vertical_operators hp hD δ hδ hδp
  have hK (a : X) : ((T a).lipBound : ℝ) ≤ Real.exp p := by
    have h := Niltest.observable_budget (hT a)
    have hB := (T a).normBound.coe_nonneg
    linarith
  have hprops := fun a =>
    hdecomp (T a).observable (T a).lipBound (T a).normBound
      (T a).lipschitz (T a).norm_le (hK a)
  let v : X → J → D.Space → ℂ := fun a j => V j (T a).observable
  have hv := fun a => (hprops a).1
  have hchar := fun a => (hprops a).2.1
  have hpres := fun a => (hprops a).2.2.1
  have herr := fun a => (hprops a).2.2.2
  let U : J → X → D.Niltest w := fun j a =>
    { orbit := (T a).orbit
      observable := v a j
      normBound := (T a).normBound
      lipBound := (T a).lipBound
      norm_le := (hv a j).2
      lipschitz := (hv a j).1 }
  have herror : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ := by
    intro a x
    simpa only [norm_sub_rev] using herr a x
  refine ⟨J, inst, eta, U, hcard, hheight, fun _ a => ⟨hT a, rfl, rfl, rfl⟩,
    fun j a => hchar a j, ?_, hpres, ?_, herror,
    contractiveFamily_integer_error D T U (fun _ _ => rfl) δ herror,
    contractiveFamily_real_error D T U (fun _ _ => rfl) δ herror⟩
  · intro j a hne z hz hGamma
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v a j)
      (hchar a j) hne z hz hGamma
  · intro j a b ε hab x
    exact hcontract j (T a).observable (T b).observable (T a).lipBound (T b).lipBound
      (T a).lipschitz (T b).lipschitz ε hab x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct Classical

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeIntervalCoordinate
namespace OAI

section

namespace Erdos3.RationalTorus

open scoped TensorProduct NNReal

noncomputable def intervalOrbit (N : ℕ) :
    (nilmanifold 1).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
  affineOrbit 1 (fun _ => 0) (fun _ : Unit => fun _ => 1 / (N : ℝ))

theorem intervalOrbit_phase (N : ℕ) [NeZero N] (x : ZMod N) :
    phaseProjection 1 ((nilmanifold 1).cyclicOrbitPoint (intervalOrbit N) N (fun _ : Unit => x)) 0 =
      ZMod.toAddCircle x := by
  unfold RationalFilteredNilmanifold.cyclicOrbitPoint intervalOrbit
  rw [phaseProjection_mk, affineOrbit_phases]
  simp [ZMod.toAddCircle_apply, div_eq_mul_inv]

theorem intervalCoordinate_lipschitz :
    letI := (nilmanifold 1).metricSpace
    LipschitzWith 1 (fun z => phaseProjection 1 z 0) := by
  let := (nilmanifold 1).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (dist_le_pi_dist (phaseProjection 1 x) (phaseProjection 1 y) 0).trans
    ((phaseProjection_lipschitz 1).dist_le_mul x y)

end Erdos3.RationalTorus

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslatedShiftTesting
namespace OAI

universe u

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct BigOperators

theorem mul {degree N : ℕ} [NeZero N] {p : ℝ} {f g : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f)
    (hg : PositiveCyclicNiltest.{u} degree N p g) (hp : 0 ≤ p) :
    PositiveCyclicNiltest.{u} degree N (productNiltestBudget (raisedNiltestBudget p))
      (fun x => f x * g x) := by
  rcases hf with @⟨L₁, lie₁, alg₁, s₁, dim₁, top₁, add₁, smul₁, t2₁, D₁, hs₁, A, hA, hAc, hevalA⟩
  rcases hg with @⟨L₂, lie₂, alg₂, s₂, dim₂, top₂, add₂, smul₂, t2₂, D₂, hs₂, B, hB, hBc, hevalB⟩
  let K : Bool → Type u := BoolLieFamily L₁ L₂
  let dims : Bool → ℕ := fun b => Bool.rec dim₂ dim₁ b
  let D : ∀ b, RationalFilteredNilmanifold (K b) degree (dims b) := fun b => by
    cases b
    · exact D₂.raiseStep hs₂
    · exact D₁.raiseStep hs₁
  let U : ∀ b, (D b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact B.raiseStep hs₂
    · exact A.raiseStep hs₁
  have hUc : ∀ b, (U b).ComplexityLE (raisedNiltestBudget p) := by
    intro b
    cases b
    · exact B.raiseStep_complexity hs₂ hp hBc
    · exact A.raiseStep_complexity hs₁ hp hAc
  have hU : ∀ b, (U b).UnitIntervalValued := by
    intro b
    cases b
    · exact B.raiseStep_unit_interval hs₂ hB
    · exact A.raiseStep_unit_interval hs₁ hA
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hcard : (Fintype.card Bool : ℝ) ≤ raisedNiltestBudget p := by
    norm_num only [Fintype.card_bool, Nat.cast_ofNat]
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (p + 2)]
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let S := RationalFilteredNilmanifold.piNiltest D U hp' hcard hUc
  have hSc := RationalFilteredNilmanifold.piNiltest_complexity D U hp' hcard hUc
  have hSu := RationalFilteredNilmanifold.piNiltest_unit_interval D U hp' hcard hUc hU
  have heval (x : ZMod N) : S.evalCyclic N (fun _ : Unit => x) =
      A.evalCyclic N (fun _ : Unit => x) * B.evalCyclic N (fun _ : Unit => x) := by
    change (RationalFilteredNilmanifold.piNiltest D U hp' hcard hUc).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    change (A.raiseStep hs₁).eval (fun _ : Unit => (x.val : ℤ)) *
      (B.raiseStep hs₂).eval (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval]
    rfl
  refine .of_test (RationalFilteredNilmanifold.pi D) le_rfl S hSu hSc ?_
  intro x
  rw [heval, Complex.mul_re, (A.unit_interval_evalCyclic hA N (fun _ => x)).1,
    (B.unit_interval_evalCyclic hB N (fun _ => x)).1, zero_mul, sub_zero, hevalA x, hevalB x]

end Erdos3.PositiveCyclicNiltest

end

section

namespace Erdos3

open scoped TensorProduct

theorem exists_interval_circle_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} 1 N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          ∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ := by
  obtain ⟨B, _, hpartition⟩ := RationalFilteredNilmanifold.exists_native_niltest_partition 1 a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p ρ hp hρ hρinv
  let D := RationalTorus.nilmanifold 1
  let G := RationalTorus.intervalOrbit N
  have hD : D.GeometryComplexityLE (p + 1) :=
    RationalTorus.nilmanifold_geometry 1 (by linarith) (by norm_num; linarith)
  have hρinv' : 1 / ρ ≤ Real.exp (((p + 1) + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) _))
  obtain ⟨n, hn, hnb, tests, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition D (fun _ : Unit => 1) (by linarith) hD hρ hρinv' G
  have hcost : (p + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  let A : Fin n → ZMod N → ℝ := fun j x => ((tests j).evalCyclic N (fun _ : Unit => x)).re
  have heval (j : Fin n) (x : ZMod N) :
      A j x = ((tests j).observable (D.cyclicOrbitPoint G N (fun _ : Unit => x))).re := by
    change ((tests j).observable (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (tests j).orbit))).re = _
    rw [horbit j]
    rfl
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A, ?_, ?_, ?_⟩
  · intro j
    exact .of_test D le_rfl (tests j) (hunit j) ((hcomplexity j).mono hcost) (fun _ => rfl)
  · intro x
    simpa only [heval] using hsum (D.cyclicOrbitPoint G N (fun _ : Unit => x))
  · let := D.metricSpace
    intro j x y hx hy
    have hd := hdiam j _ _ ((heval j x) ▸ hx) ((heval j y) ▸ hy)
    have hp := RationalTorus.intervalCoordinate_lipschitz.dist_le_mul
      (D.cyclicOrbitPoint G N (fun _ : Unit => x)) (D.cyclicOrbitPoint G N (fun _ : Unit => y))
    change dist (RationalTorus.phaseProjection 1 (D.cyclicOrbitPoint G N (fun _ : Unit => x)) 0)
      (RationalTorus.phaseProjection 1 (D.cyclicOrbitPoint G N (fun _ : Unit => y)) 0) ≤
      (1 : ℝ) * dist (D.cyclicOrbitPoint G N (fun _ : Unit => x))
        (D.cyclicOrbitPoint G N (fun _ : Unit => y)) at hp
    rw [RationalTorus.intervalOrbit_phase, RationalTorus.intervalOrbit_phase, one_mul] at hp
    exact hp.trans hd

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeResidueNiltests
namespace OAI

section

namespace Erdos3.RationalTorus

open CircleFourier
open scoped TensorProduct NNReal

theorem residueObservable_lipschitz {q : ℕ} [NeZero q] (j : ZMod q) :
    LipschitzWith (q : ℝ≥0) (fun v : Fin 1 → CircleFourier.Circle => residueCutoff j (v 0)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  exact ((residueCutoff_lipschitz j).dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (dist_le_pi_dist v w 0) (Nat.cast_nonneg q))

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra 1)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra 1)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra 1)] [T2Space (ℝ ⊗[ℚ] Algebra 1)]

noncomputable def residueNiltest {q : ℕ} [NeZero q] (j : ZMod q) :
    (nilmanifold 1).Niltest (fun _ : Unit => 1) :=
  realAffineNiltest (Equiv.refl (Fin 1)) (fun v => residueCutoff j (v 0))
    (fun _ => 0) (fun _ => 1 / (q : ℝ)) (q : ℝ≥0)
    (fun v => residueCutoff_unit_interval j (v 0)) (residueObservable_lipschitz j)

theorem residueNiltest_unit_interval {q : ℕ} [NeZero q] (j : ZMod q) :
    (residueNiltest j).UnitIntervalValued := by
  unfold residueNiltest
  apply realAffineNiltest_unitInterval

theorem residueNiltest_complexity {q : ℕ} [NeZero q] (j : ZMod q) {p : ℝ}
    (hp : 0 ≤ p) (hq : (q : ℝ) ≤ Real.exp p) :
    (residueNiltest j).ComplexityLE (p + 2) := by
  unfold residueNiltest
  apply realAffineNiltest_complexity _ _ _ _ _ _ _ (by linarith) (by norm_num; linarith)
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have h1 := Real.one_le_exp hp
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  change 3 + (q : ℝ) ≤ Real.exp p * Real.exp 2
  nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg p)]

theorem residueNiltest_evalCyclic {q : ℕ} [NeZero q] (j : ZMod q)
    (N : ℕ) [NeZero N] (x : ZMod N) :
    (residueNiltest j).evalCyclic N (fun _ : Unit => x) =
      if (x.val : ZMod q) = j then 1 else 0 := by
  classical
  unfold residueNiltest
  rw [realAffineNiltest_evalCyclic]
  simp only [zero_add, mul_one_div]
  rw [← ZMod.toAddCircle_natCast, residueCutoff_at_grid]
  split_ifs <;> rfl

end Erdos3.RationalTorus

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntervalResiduePartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residue_indicator_positiveCyclicNiltest {q N : ℕ} [NeZero q] [NeZero N]
    (j : ZMod q) {p : ℝ} (hp : 0 ≤ p) (hq : (q : ℝ) ≤ Real.exp p) :
    PositiveCyclicNiltest.{0} 1 N (p + 2)
      (fun x => if (x.val : ZMod q) = j then 1 else 0) := by
  classical
  refine .of_test (RationalTorus.nilmanifold 1) le_rfl (RationalTorus.residueNiltest j)
    (RationalTorus.residueNiltest_unit_interval j) (RationalTorus.residueNiltest_complexity j hp hq) ?_
  intro x
  rw [RationalTorus.residueNiltest_evalCyclic]
  split_ifs <;> rfl

theorem refine_positive_partition_by_residue {I : Type*} [Fintype I]
    {degree q N : ℕ} [NeZero q] [NeZero N] (A : I → ZMod N → ℝ) {p : ℝ}
    (hp : 0 ≤ p) (hdegree : 1 ≤ degree) (hq : (q : ℝ) ≤ Real.exp p)
    (hA : ∀ i, PositiveCyclicNiltest.{0} degree N p (A i)) (hsum : ∀ x, ∑ i, A i x = 1) :
    ∃ B : (I × ZMod q) → ZMod N → ℝ,
      (∀ j, PositiveCyclicNiltest.{0} degree N
        (productNiltestBudget (raisedNiltestBudget (p + 2))) (B j)) ∧
      (∀ x, ∑ j, B j x = 1) ∧
      (∀ j x, 0 < B j x → 0 < A j.1 x ∧ (x.val : ZMod q) = j.2) := by
  classical
  let B : (I × ZMod q) → ZMod N → ℝ := fun j x =>
    A j.1 x * if (x.val : ZMod q) = j.2 then 1 else 0
  refine ⟨B, ?_, ?_, ?_⟩
  · intro j
    exact ((hA j.1).mono le_rfl (by linarith)).mul
      ((residue_indicator_positiveCyclicNiltest j.2 hp hq).mono hdegree le_rfl) (by linarith)
  · intro x
    simpa [B, Fintype.sum_prod_type, mul_ite] using hsum x
  · intro j x hx
    by_cases h : (x.val : ZMod q) = j.2
    · exact ⟨by simpa only [B, h, ↓reduceIte, mul_one] using hx, h⟩
    · simp only [B, h, ↓reduceIte, mul_zero, lt_self_iff_false] at hx

theorem exists_controlled_residue_refinement :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I]
      {degree q N : ℕ} [NeZero q] [NeZero N] (A : I → ZMod N → ℝ) {p : ℝ},
      0 ≤ p → 1 ≤ degree → (Fintype.card I : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      (∀ i, PositiveCyclicNiltest.{0} degree N p (A i)) → (∀ x, ∑ i, A i x = 1) →
      ∃ B : (I × ZMod q) → ZMod N → ℝ,
        (Fintype.card (I × ZMod q) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ j, PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (B j)) ∧
        (∀ x, ∑ j, B j x = 1) ∧
        ∀ j x, 0 < B j x → 0 < A j.1 x ∧ (x.val : ZMod q) = j.2 := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 2) + (X + 4) ^ 2 + 3
  let Q := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + Q)
  refine ⟨C, hC, ?_⟩
  intro I _ degree q N _ _ A p hp hdegree hcard hq hA hsum
  obtain ⟨B, hB, hBsum, hsupport⟩ := refine_positive_partition_by_residue A hp hdegree hq hA hsum
  have hcost : 2 * p + productNiltestBudget (raisedNiltestBudget (p + 2)) ≤ (p + C) ^ C := by
    simpa [X, Q, R, Polynomial.eval₂_pow, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, show p + 2 + 2 = p + 4 by ring] using hbudget p hp
  have hnonneg : 0 ≤ productNiltestBudget (raisedNiltestBudget (p + 2)) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  refine ⟨B, ?_, fun j => (hB j).mono le_rfl (by linarith), hBsum, hsupport⟩
  calc
    _ = (Fintype.card I : ℝ) * q := by rw [Fintype.card_prod, ZMod.card, Nat.cast_mul]
    _ ≤ Real.exp p * Real.exp p := mul_le_mul hcard hq (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_interval_residue_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N M : ℕ) [NeZero N] [NeZero M] {p ρ : ℝ},
      0 ≤ p → (M : ℝ) ≤ Real.exp p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (Fintype.card (Fin n × ZMod M) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : (Fin n × ZMod M) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} 1 N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          ∀ j x y, x ∉ cyclicWrapExceptional 0 ρ → y ∉ cyclicWrapExceptional 0 ρ →
            0 < A j x → 0 < A j y →
            |(x.val : ℝ) - y.val| ≤ N * ρ ∧ (M : ℤ) ∣ (x.val : ℤ) - y.val := by
  obtain ⟨b, _, hpart⟩ := exists_interval_circle_partition a
  obtain ⟨c, _, hrefine⟩ := exists_controlled_residue_refinement
  let B : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((B + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro N M _ _ p ρ hp hM hρ hprec
  classical
  obtain ⟨n, hn, hnb, V, hV, hsum, hdiam⟩ := hpart N hp hρ hprec
  let t := p + (p + b) ^ b
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hbt : (p + b) ^ b ≤ t := le_add_of_nonneg_left hp
  have hcost : (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, t, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, hcard, hA, hAsum, hsupport⟩ := hrefine V (hp.trans hpt) le_rfl
    (by simpa only [Fintype.card_fin] using hnb.trans (Real.exp_le_exp.mpr hbt))
    (hM.trans (Real.exp_le_exp.mpr hpt)) (fun j => (hV j).mono le_rfl hbt) hsum
  refine ⟨n, hn, hcard.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hAsum, ?_⟩
  intro j x y hx hy hAx hAy
  obtain ⟨hVx, hMx⟩ := hsupport j x hAx
  obtain ⟨hVy, hMy⟩ := hsupport j y hAy
  have hnear := good_circle_observations_control_representatives 0 x y hρ hx hy
    (hdiam j.1 x y hVx hVy)
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [← sub_div, abs_div, abs_of_pos hN] at hnear
  refine ⟨by simpa only [mul_comm] using (div_le_iff₀ hN).mp hnear, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((x.val : ℤ) - y.val) M).mp
  push_cast
  rw [hMx, hMy, sub_self]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyPrecenterProjectionData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L σ G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def kernelProjection (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) : D.Niltest w := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  exact T.averageCircles
    (fun i => D.centralRationalCircle (b i).val (hK (b i).property))
    (List.finRange (finrank ℚ K))

theorem kernelProjection_orbit (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) :
    (T.kernelProjection K hK).orbit = T.orbit := rfl

theorem kernelProjection_congr (T : D.Niltest w) {K K' : Submodule ℚ L}
    (hK : K ≤ D.filtration.layer s) (hK' : K' ≤ D.filtration.layer s) (h : K = K') :
    T.kernelProjection K hK = T.kernelProjection K' hK' := by
  subst K'
  rfl

theorem kernelProjection_complexity (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.kernelProjection K hK).ComplexityLE p := hT

theorem kernelProjection_unitInterval (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (hT : T.UnitIntervalValued) :
    (T.kernelProjection K hK).UnitIntervalValued := by
  unfold kernelProjection
  exact T.averageCircles_unit_interval _ _ hT

theorem kernelProjection_invariant (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (z : D.RealGroup) (hz : z.coord ∈ K.baseChange ℝ) (x : D.Space) :
    (T.kernelProjection K hK).observable (z • x) = (T.kernelProjection K hK).observable x := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  apply D.invariant_of_kernel_circles K hK b _ _ z hz x
  intro i t y
  apply T.averageCircles_invariant
  · dsimp only
    intro j _ k _
    exact D.centralRationalCircle_commutes (b j).val (b k).val (hK (b j).property) (hK (b k).property)
  · simp

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators

variable {L σ X G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_external_family_centralRationalCircle_frequency
    (v : L) (hv : v ∈ D.filtration.layer s)
    (eta : L →ₗ[ℚ] ℚ) (f : X → D.Space → ℂ)
    (hf : ∀ a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      f a (z • x) =
        character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * f a x) :
    let := D.metricSpace
    ∃ n : ℤ,
      (∀ a t x, f a ((D.centralRationalCircle v hv).act t x) =
        character (n • t) * f a x) ∧
      (eta v = 0 → n = 0) := by
  classical
  let := D.metricSpace
  by_cases hz : ∀ a x, f a x = 0
  · exact ⟨0, fun a t x => by simp [hz], fun _ => rfl⟩
  push Not at hz
  obtain ⟨a, x, hax⟩ := hz
  obtain ⟨n, hn⟩ := vertical_frequency_integral_on_lattice D.filtration D.realLattice
    eta (f a) (hf a) ⟨x, hax⟩ (⟨D.periodicRealDirection v⟩ : D.RealGroup)
    (D.periodicRealDirection_mem_top v hv) (D.periodicRealDirection_mem_lattice v)
  refine ⟨n, ?_, ?_⟩
  · intro a t x
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [D.centralRationalCircle_act_coe]
    have hr : realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.periodicRealDirection v) r ∈ D.filtration.realification.subgroup s := by
      change r • D.periodicRealDirection v ∈ D.filtration.realLayer s
      exact (D.filtration.realLayer s).smul_mem r (D.periodicRealDirection_mem_top v hv)
    rw [hf a _ hr]
    apply congrArg (fun z : CircleFourier.Circle => character z * f a x)
    change ((realifyFunctional eta (r • D.periodicRealDirection v) : ℝ) : CircleFourier.Circle) =
      n • (r : CircleFourier.Circle)
    rw [map_smul, hn, ← AddCircle.coe_zsmul]
    congr 1
    simp only [smul_eq_mul, zsmul_eq_mul, mul_comm]
  · intro heta
    have hzero : realifyFunctional eta (D.periodicRealDirection v) = 0 := by
      simp [periodicRealDirection, realifyFunctional_tmul, heta]
    have hn0 : (n : ℝ) = 0 := hn.symm.trans hzero
    exact_mod_cast hn0

namespace Niltest

theorem external_family_kernelProjection_tested_error [Fintype G]
    (T : X → D.Niltest w) (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    {J : Type*} [Fintype J] (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
    (hvertical : ∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j a).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
          (U j a).observable x)
    (law : FiniteProbabilityWeights G) (physical : G → X)
    (path : G → D.Space) (weight : G → ℂ)
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ rho)
    (js : List J)
    (hsignificant : ∀ j,
      tau < ‖law.complexMean (fun x => weight x * (U j (physical x)).observable (path x))‖ →
        j ∈ js) :
    ‖law.complexMean (fun x => weight x * (T (physical x)).observable (path x)) -
      law.complexMean (fun x => weight x *
        ((T (physical x)).kernelProjection (finiteFrequencyKernel P eta js)
          ((finiteFrequencyKernel_le P eta js).trans hP)).observable (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let K := finiteFrequencyKernel P eta js
  have hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P eta js).trans hP
  let b := Module.finBasis ℚ K
  let A := fun i => D.centralRationalCircle (b i).val (hK (b i).property)
  have hfreq (j : J) (i : Fin (finrank ℚ K)) : ∃ n : ℤ,
      (∀ a t x, (U j a).observable ((A i).act t x) =
        character (n • t) * (U j a).observable x) ∧
      (eta j (b i).val = 0 → n = 0) :=
    exists_external_family_centralRationalCircle_frequency (b i).val (hK (b i).property)
      (eta j) (fun a => (U j a).observable) (hvertical j)
  choose n heigen hzero using hfreq
  apply iteratedCircleAverage_family_tested_weighted_error law A
    (List.finRange (finrank ℚ K)) (fun a => (T a).observable)
    (fun j a => (U j a).observable) n physical path weight
    (fun a => (T a).lipBound) (fun j a => (U j a).lipBound)
    (fun a => (T a).lipschitz) (fun j a => (U j a).lipschitz)
    hB htau hweight happrox (fun j i _ t a x => heigen j i a t x)
  intro j hj
  apply le_of_not_gt
  intro hlarge
  apply hj
  intro i _
  apply hzero j i
  exact ((mem_finiteFrequencyKernel P eta js (b i).val).mp (b i).property).2 j
    (hsignificant j hlarge)

end Niltest

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem kernelProjection_observable_sub_norm_le (T : D.Niltest w) (U : D.Niltest v)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) {ε : ℝ}
    (hTU : ∀ x, ‖T.observable x - U.observable x‖ ≤ ε) :
    ∀ x, ‖(T.kernelProjection K hK).observable x - (U.kernelProjection K hK).observable x‖ ≤ ε := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  exact iteratedCircleAverage_sub_norm_le
    (fun i => D.centralRationalCircle (b i).val (hK (b i).property))
    (List.finRange (finrank ℚ K)) T.lipschitz U.lipschitz hTU

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier MeasureTheory
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_iteratedCentralCircle_translation (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (v : ι → K) (is : List ι)
    (t : CircleAverageTuple is) :
    let := D.metricSpace
    ∃ g : D.RealGroup, g.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅g.coord, y⁆ = 0) ∧
      ∀ x, iteratedCircleAction
        (fun i => D.centralRationalCircle (v i) (hK (v i).property)) is t x = g • x := by
  let := D.metricSpace
  induction is with
  | nil =>
    refine ⟨1, (K.baseChange ℝ).zero_mem, fun y => zero_lie y, ?_⟩
    intro x
    exact (one_smul D.RealGroup x).symm
  | cons i is ih =>
    obtain ⟨g, hg, hcentral, hact⟩ := ih t.2
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective t.1
    let z : D.RealGroup := realBCHLine (D.periodicRealDirection (v i)) r
    have hz : z.coord ∈ K.baseChange ℝ := by
      apply (K.baseChange ℝ).smul_mem r
      change (1 : ℝ) ⊗ₜ[ℚ] ((D.rationalDirectionPeriod (v i) : ℚ) • (v i : L)) ∈ _
      exact Submodule.tmul_mem_baseChange_of_mem 1 (K.smul_mem _ (v i).property)
    have hzc : ∀ y : ℝ ⊗[ℚ] L, ⁅z.coord, y⁆ = 0 := by
      intro y
      change ⁅r • D.periodicRealDirection (v i), y⁆ = 0
      rw [smul_lie, D.periodicRealDirection_central (v i) (hK (v i).property), smul_zero]
    have hcoord : (g * z).coord = g.coord + z.coord :=
      lieBCH_eq_add_of_lie_eq_zero D.filtration.realification.lowerCentralSeries_eq_bot
        (hcentral z.coord)
    refine ⟨g * z, ?_, ?_, ?_⟩
    · rw [hcoord]
      exact (K.baseChange ℝ).add_mem hg hz
    · intro y
      rw [hcoord, add_lie, hcentral, hzc, add_zero]
    · intro x
      change iteratedCircleAction _ is t.2
        ((D.centralRationalCircle (v i) (hK (v i).property)).act t.1 x) = _
      rw [hact, ← hr, D.centralRationalCircle_act_coe, mul_smul]

abbrev KernelProjectionParameters (K : Submodule ℚ L) :=
  CircleAverageTuple (List.finRange (finrank ℚ K))

noncomputable def kernelProjectionCircleFamily (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) :
    let := D.metricSpace
    Fin (finrank ℚ K) → IsometricCircleAction D.Space := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact fun i => D.centralRationalCircle (Module.finBasis ℚ K i)
    (hK (Module.finBasis ℚ K i).property)

theorem exists_kernelProjectionTranslation (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) :
    let := D.metricSpace
    ∃ g : D.RealGroup, g.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅g.coord, y⁆ = 0) ∧
      ∀ x, iteratedCircleAction (D.kernelProjectionCircleFamily K hK)
        (List.finRange (finrank ℚ K)) t x = g • x := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact D.exists_iteratedCentralCircle_translation K hK (Module.finBasis ℚ K)
    (List.finRange (finrank ℚ K)) t

noncomputable def kernelProjectionTranslation (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) : D.RealGroup :=
  (D.exists_kernelProjectionTranslation K hK t).choose

theorem kernelProjectionTranslation_mem (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) :
    (D.kernelProjectionTranslation K hK t).coord ∈ K.baseChange ℝ :=
  (D.exists_kernelProjectionTranslation K hK t).choose_spec.1

theorem kernelProjectionTranslation_central (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K)
    (y : ℝ ⊗[ℚ] L) : ⁅(D.kernelProjectionTranslation K hK t).coord, y⁆ = 0 :=
  (D.exists_kernelProjectionTranslation K hK t).choose_spec.2.1 y

theorem kernelProjectionTranslation_act (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) (x : D.Space) :
    let := D.metricSpace
    iteratedCircleAction (D.kernelProjectionCircleFamily K hK)
      (List.finRange (finrank ℚ K)) t x = D.kernelProjectionTranslation K hK t • x :=
  (D.exists_kernelProjectionTranslation K hK t).choose_spec.2.2 x

theorem continuous_kernelProjectionTranslation_act (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    let := D.metricSpace
    Continuous (fun t => D.kernelProjectionTranslation K hK t • x) := by
  let := D.metricSpace
  have he : (fun t => D.kernelProjectionTranslation K hK t • x) =
      (fun t => iteratedCircleAction (D.kernelProjectionCircleFamily K hK)
        (List.finRange (finrank ℚ K)) t x) :=
    funext (fun t => (D.kernelProjectionTranslation_act K hK t x).symm)
  rw [he]
  exact continuous_iteratedCircleAction_parameter _ _ _

namespace Niltest

variable {D} {σ : Type*} {w : σ → ℕ}

theorem continuous_kernelProjectionTranslation_observable (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    Continuous (fun t => T.observable (D.kernelProjectionTranslation K hK t • x)) := by
  let := D.metricSpace
  exact T.lipschitz.continuous.comp (D.continuous_kernelProjectionTranslation_act K hK x)

theorem integrable_kernelProjectionTranslation_observable (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    Integrable (fun t => T.observable (D.kernelProjectionTranslation K hK t • x))
      (circleAverageTupleMeasure (List.finRange (finrank ℚ K))) :=
  (T.continuous_kernelProjectionTranslation_observable K hK x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem kernelProjection_observable_eq_integral (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    (T.kernelProjection K hK).observable x =
      ∫ t, T.observable (D.kernelProjectionTranslation K hK t • x)
        ∂circleAverageTupleMeasure (List.finRange (finrank ℚ K)) := by
  let := D.metricSpace
  change iteratedCircleAverage (D.kernelProjectionCircleFamily K hK)
    (List.finRange (finrank ℚ K)) T.observable x = _
  rw [iteratedCircleAverage_eq_integral _ _ T.lipschitz.continuous]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => congrArg T.observable
    (D.kernelProjectionTranslation_act K hK t x))

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_external_family_common_positive_kernel_projection
    {L σ X Ω G J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype G] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : X → D.Niltest w) (hT : ∀ x, (T x).UnitIntervalValued)
    {p : ℝ} (hTc : ∀ x, (T x).ComplexityLE p)
    (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
    (hvertical : ∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j a).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
          (U j a).observable x)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
    (path : Ω → G → D.Space) (weight : Ω → G → ℂ)
    {B rho tau delta : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ a x, ‖weight a x‖ ≤ B)
    (happrox : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ rho)
    (hscore : ∀ a ∈ productive,
      delta ≤ ((localLaw a).complexMean (fun x =>
        weight a x * (T (physical a x)).observable (path a x))).re)
    (hsmall : 2 * B * rho + Fintype.card J * tau ≤ delta / 2) :
    ∃ (code : Fin (finrank ℚ P) → Option J) (S : X → D.Niltest w)
      (retained : Finset Ω),
      (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
        ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
      (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE p ∧ (S x).orbit = (T x).orbit) ∧
      (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
        ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
      retained ⊆ productive ∧
      outer.mass productive / (Fintype.card J + 1) ^ finrank ℚ P ≤ outer.mass retained ∧
      ∀ a ∈ retained,
        (∀ i j, code i = some j →
          tau < ‖(localLaw a).complexMean (fun x =>
            weight a x * (U j (physical a x)).observable (path a x))‖) ∧
        delta / 2 ≤ ((localLaw a).complexMean (fun x =>
          weight a x * (S (physical a x)).observable (path a x))).re := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let js : Ω → List J := fun a => (Finset.univ.filter (fun j =>
    tau < ‖(localLaw a).complexMean (fun x =>
      weight a x * (U j (physical a x)).observable (path a x))‖)).toList
  obtain ⟨code, retained, hretained, hmass, hcode⟩ :=
    exists_common_frequency_kernel outer productive P eta js
  let K := frequencyCodeKernel P eta code
  have hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans hP
  let S := fun x => (T x).kernelProjection K hK
  refine ⟨code, S, retained, fun _ => rfl, ?_, ?_, hretained, hmass, ?_⟩
  · intro x
    exact ⟨(T x).kernelProjection_unitInterval K hK (hT x),
      (T x).kernelProjection_complexity K hK (hTc x), (T x).kernelProjection_orbit K hK⟩
  · intro a z hz x
    exact (T a).kernelProjection_invariant K hK z hz x
  · intro a ha
    obtain ⟨hpivots, hk⟩ := hcode a ha
    have hsignificant (j : J)
        (hj : tau < ‖(localLaw a).complexMean (fun x =>
          weight a x * (U j (physical a x)).observable (path a x))‖) : j ∈ js a := by
      simpa only [js, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have herr := external_family_kernelProjection_tested_error T P hP eta U hvertical
      (localLaw a) (physical a) (path a) (weight a) hB htau (hweight a) happrox
      (js a) hsignificant
    have hproj (x : X) : (T x).kernelProjection (finiteFrequencyKernel P eta (js a))
        ((finiteFrequencyKernel_le P eta (js a)).trans hP) = S x :=
      (T x).kernelProjection_congr _ hK hk
    simp_rw [hproj] at herr
    refine ⟨?_, ?_⟩
    · intro i j hij
      simpa only [js, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
        using hpivots i j hij
    · have hr := Complex.re_le_norm
        ((localLaw a).complexMean (fun x => weight a x * (T (physical a x)).observable (path a x)) -
          (localLaw a).complexMean (fun x => weight a x * (S (physical a x)).observable (path a x)))
      rw [Complex.sub_re] at hr
      have hs := hscore a (hretained ha)
      linarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_external_family_precenter_kernel_projection_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : X → D.Niltest w) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (∀ x, (T x).UnitIntervalValued) → (∀ x, (T x).ComplexityLE p) →
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j x, (U j x).ComplexityLE ((p + 2) ^ C) ∧
          (U j x).orbit = (T x).orbit ∧ (U j x).normBound = (T x).normBound ∧
          (U j x).lipBound = (T x).lipBound) ∧
        (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j a).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
              (U j a).observable x) ∧
        (∀ j a b (ε : ℝ),
          (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
          ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε) ∧
      ∀ {Ω G : Type*} [Fintype Ω] [Fintype G],
      ∀ (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s),
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
        (path : Ω → G → D.Space) (weight : Ω → G → ℂ),
      (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
      (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
        (fun x => weight a x * (T (physical a x)).observable (path a x))).re) →
      ∃ (code : Fin (finrank ℚ P) → Option J) (S : X → D.Niltest w)
        (retained : Finset Ω),
        (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE ((p + 2) ^ C) ∧
          (S x).orbit = (T x).orbit) ∧
        (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
          ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
        (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
          ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained,
          (∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
            ‖(localLaw a).complexMean (fun x =>
              weight a x * (U j (physical a x)).observable (path a x))‖) ∧
          Real.exp (-((p + 2) ^ C)) ≤ ((localLaw a).complexMean
            (fun x => weight a x * (S (physical a x)).observable (path a x))).re := by
  let R : Polynomial ℕ := Polynomial.X
  let Q := 2 * R + 8
  let A := (Q + 3) ^ 9 + 2 * Q + 2
  let V := 2 * A * (2 * A + 2) ^ 4 + ((2 * A + 2) ^ 4 + A + (Q + 3) ^ 5 + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Q + 2 * V + R + 10 + R * (V + 1))
  refine ⟨C, hC, ?_⟩
  intro L σ X _ _ s d _ _ _ _ D w T p hp hD hT hTc
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let q := 2 * p + 8
  let v := verticalDecompositionBudget q
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hv : 0 ≤ v := verticalDecompositionBudget_nonneg hq
  have hprod : 0 ≤ p * (v + 1) := by positivity
  have hb : q + 2 * v + p + 10 + p * (v + 1) ≤ (p + 2) ^ C := by
    simpa [R, Q, A, V, q, v, verticalDecompositionBudget, centralActionBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  have hvC : v ≤ (p + 2) ^ C := by linarith
  have htC : p + v + 8 ≤ (p + 2) ^ C := by linarith
  have hnC : p * (v + 1) ≤ (p + 2) ^ C := by linarith
  have hsC : p + 1 ≤ (p + 2) ^ C := by linarith
  obtain ⟨J, inst, eta, U, hJ, hheight, hU, hvert, hint, hchar, hcontract, happrox, hintError, hrealError⟩ :=
    D.exists_externalFamily_contractive_vertical_expansion hq (hD.mono D hpq) T
      (fun x => (hTc x).mono hpq) (Real.exp (-q)) (Real.exp_pos (-q))
      (by rw [Real.exp_neg, inv_inv])
  let _ := inst
  refine ⟨J, inst, eta, U,
    hJ.trans (Real.exp_le_exp.mpr hvC), fun j i => (hheight j i).trans hvC,
    fun j x => ⟨(hU j x).1.mono hqC, (hU j x).2⟩, hvert, hcontract, ?_⟩
  intro Ω G _ _ P hP outer productive localLaw physical path weight hweight hscore
  have hsmall := frequency_projection_error_bound hp hJ
  obtain ⟨code, S, retained, hidentity, hS, hSinv, hretained, hmass, hlocal⟩ :=
    RationalFilteredNilmanifold.Niltest.exists_external_family_common_positive_kernel_projection
      T hT hTc P hP eta U hvert outer productive localLaw physical path weight
      (Real.exp_nonneg p) (Real.exp_nonneg (-(p + v + 8))) hweight happrox hscore hsmall
  have hdim : (finrank ℚ P : ℝ) ≤ p := by
    have h := Submodule.finrank_le P
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at h
    exact (Nat.cast_le.mpr h).trans hD.1
  refine ⟨code, S, retained,
    fun x => ⟨(hS x).1, (hS x).2.1.mono (hpq.trans hqC), (hS x).2.2⟩,
    hidentity, hSinv, hretained, ?_, ?_⟩
  · exact (mass_div_frequency_count (outer.mass_nonneg productive) hp hv hdim hJ hnC).trans hmass
  · intro a ha
    obtain ⟨hpivot, hpositive⟩ := hlocal a ha
    refine ⟨fun i j hij => (Real.exp_le_exp.mpr (neg_le_neg htC)).trans_lt (hpivot i j hij), ?_⟩
    exact ((Real.exp_le_exp.mpr (by linarith : -((p + 2) ^ C) ≤ -p - 1)).trans
      (exp_sub_one_le_half_exp (-p))).trans hpositive

end Erdos3

end

section

namespace Erdos3
open Module CircleFourier
open scoped TensorProduct BigOperators Classical

structure ExternalFamilyPrecenterProjectionData
    {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : X → D.Niltest w) (p q : ℝ) where
  Freq : Type
  instFintype : Fintype Freq
  eta : Freq → L →ₗ[ℚ] ℚ
  U : Freq → X → D.Niltest w
  card_bound : (@Fintype.card Freq instFintype : ℝ) ≤ Real.exp q
  eta_height : ∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ q
  U_bounds : ∀ j x, (U j x).ComplexityLE q ∧
    (U j x).orbit = (T x).orbit ∧ (U j x).normBound = (T x).normBound ∧
    (U j x).lipBound = (T x).lipBound
  vertical : ∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
    (U j a).observable (z • x) =
      character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
        (U j a).observable x
  contractive : ∀ j a b (ε : ℝ),
    (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
    ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε
  select : ∀ {Ω G : Type} [Fintype Ω] [Fintype G],
    ∀ (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s),
    ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
      (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
      (path : Ω → G → D.Space) (weight : Ω → G → ℂ),
    (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
    (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
      (fun x => weight a x * (T (physical a x)).observable (path a x))).re) →
    ∃ (code : Fin (finrank ℚ P) → Option Freq) (S : X → D.Niltest w)
      (retained : Finset Ω),
      (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE q ∧
        (S x).orbit = (T x).orbit) ∧
      (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
        ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
      (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
        ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
      retained ⊆ productive ∧
      outer.mass productive * Real.exp (-q) ≤ outer.mass retained ∧
      ∀ a ∈ retained,
        (∀ i j, code i = some j → Real.exp (-q) <
          ‖(localLaw a).complexMean (fun x =>
            weight a x * (U j (physical a x)).observable (path a x))‖) ∧
        Real.exp (-q) ≤ ((localLaw a).complexMean
          (fun x => weight a x * (S (physical a x)).observable (path a x))).re

attribute [instance] ExternalFamilyPrecenterProjectionData.instFintype

theorem exists_externalFamilyPrecenterProjectionData :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : X → D.Niltest w) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (∀ x, (T x).UnitIntervalValued) → (∀ x, (T x).ComplexityLE p) →
      Nonempty (ExternalFamilyPrecenterProjectionData T p ((p + 2) ^ C)) := by
  obtain ⟨C, hC, hproduce⟩ := exists_external_family_precenter_kernel_projection_budget
  refine ⟨C, hC, ?_⟩
  intro L σ X _ _ s d _ _ _ _ D w T p hp hD hT hTc
  obtain ⟨J, inst, eta, U, hJ, hheight, hU, hvert, hcontract, hselect⟩ :=
    hproduce T p hp hD hT hTc
  exact ⟨{
    Freq := J
    instFintype := inst
    eta := eta
    U := U
    card_bound := hJ
    eta_height := hheight
    U_bounds := hU
    vertical := hvert
    contractive := hcontract
    select := hselect }⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativePrescribedProjection
namespace OAI

section

namespace Erdos3.CircleFourier.IsometricCircleAction

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def project (A : IsometricCircleAction X) (n : ℤ) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  circleFourierComponent n f

theorem project_character (A : IsometricCircleAction X) (n : ℤ) (f : X → ℂ)
    (t : Circle) (x : X) :
    A.project n f (A.act t x) = character (n • t) * A.project n f x := by
  let := A.toAddAction
  exact circleFourierComponent_vadd n f t x

theorem project_lipschitz (A : IsometricCircleAction X) (n : ℤ) {f : X → ℂ}
    {K : ℝ≥0} (hf : LipschitzWith K f) : LipschitzWith K (A.project n f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_circleFourierComponent n hf A.isometry_act

theorem project_norm_le (A : IsometricCircleAction X) (n : ℤ) {f : X → ℂ}
    {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖A.project n f x‖ ≤ B := by
  let := A.toAddAction
  exact norm_circleFourierComponent_le n f hf x

theorem project_equivariant (A : IsometricCircleAction X) (n : ℤ) {f : X → ℂ}
    (g : X → X) (z : ℂ) (hg : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.project n f (g x) = z * A.project n f x := by
  unfold project circleFourierComponent
  change (∫ t : Circle, character ((-n) • t) * f (A.act t (g x)) ∂circleHaar) =
    z * (∫ t : Circle, character ((-n) • t) * f (A.act t x) ∂circleHaar)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hg, hf]
  ring

theorem project_eq_at (A : IsometricCircleAction X) (n : ℤ) (f : X → ℂ) (x : X)
    (hx : ∀ t, f (A.act t x) = character (n • t) * f x) : A.project n f x = f x := by
  unfold project circleFourierComponent
  change (∫ t : Circle, character ((-n) • t) * f (A.act t x) ∂circleHaar) = _
  have heq (t : Circle) : character ((-n) • t) * f (A.act t x) = f x := by
    rw [hx, ← mul_assoc, ← character_add, ← add_smul]
    simp only [neg_add_cancel, zero_smul, character_zero, one_mul]
  simp_rw [heq]
  simp

end Erdos3.CircleFourier.IsometricCircleAction

end

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedExactProjection (A : α → IsometricCircleAction X) (n : α → ℤ) :
    List α → (X → ℂ) → X → ℂ
  | [], f => f
  | i :: is, f => (A i).project (n i) (iteratedExactProjection A n is f)

theorem iteratedExactProjection_lipschitz (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) {f : X → ℂ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (iteratedExactProjection A n is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).project_lipschitz (n i) ih

theorem iteratedExactProjection_norm_le (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) {f : X → ℂ} {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedExactProjection A n is f x‖ ≤ B := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).project_norm_le (n i) ih

theorem iteratedExactProjection_character (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j)) (f : X → ℂ)
    (j : α) (hj : j ∈ is) (t : Circle) (x : X) :
    iteratedExactProjection A n is f ((A j).act t x) =
      character (n j • t) * iteratedExactProjection A n is f x := by
  induction is generalizing x with
  | nil => simp only [List.not_mem_nil] at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with rfl | hj
    · exact (A j).project_character (n j) _ t x
    · apply (A i).project_equivariant (n i) ((A j).act t) (character (n j • t))
      · exact fun u y => hcomm i List.mem_cons_self j (List.mem_cons_of_mem i hj) u t y
      · intro y
        exact ih (fun a ha b hb => hcomm a (List.mem_cons_of_mem i ha) b
          (List.mem_cons_of_mem i hb)) hj y

theorem iteratedExactProjection_eq_on (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) (S : Set X) (f : X → ℂ)
    (hstable : ∀ i ∈ is, ∀ t x, x ∈ S → (A i).act t x ∈ S)
    (hchar : ∀ i ∈ is, ∀ t x, x ∈ S → f ((A i).act t x) = character (n i • t) * f x) :
    ∀ x ∈ S, iteratedExactProjection A n is f x = f x := by
  induction is with
  | nil => exact fun _ _ => rfl
  | cons i is ih =>
    have htail := ih (fun j hj => hstable j (List.mem_cons_of_mem i hj))
      (fun j hj => hchar j (List.mem_cons_of_mem i hj))
    intro x hx
    change (A i).project (n i) (iteratedExactProjection A n is f) x = f x
    rw [(A i).project_eq_at (n i) _ x]
    · exact htail x hx
    · intro t
      rw [htail _ (hstable i List.mem_cons_self t x hx), htail x hx]
      exact hchar i List.mem_cons_self t x hx

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped NNReal

theorem exists_prescribed_circle_projection {X α : Type*} [PseudoMetricSpace X] [Fintype α]
    (A : α → IsometricCircleAction X) (n : α → ℤ)
    (hcomm : ∀ i j, (A i).Commutes (A j)) (S : Set X) (f : X → ℂ)
    (hstable : ∀ i t x, x ∈ S → (A i).act t x ∈ S)
    (hchar : ∀ i t x, x ∈ S → f ((A i).act t x) = character (n i • t) * f x)
    {K : ℝ≥0} {B : ℝ} (hf : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ B) ∧
      (∀ i t x, g ((A i).act t x) = character (n i • t) * g x) ∧
      ∀ x ∈ S, g x = f x := by
  classical
  let is := (Finset.univ : Finset α).toList
  refine ⟨iteratedExactProjection A n is f, iteratedExactProjection_lipschitz A n is hf,
    iteratedExactProjection_norm_le A n is hb, ?_, ?_⟩
  · intro j t x
    exact iteratedExactProjection_character A n is (fun i _ j _ => hcomm i j) f j
      (by simp [is]) t x
  · exact iteratedExactProjection_eq_on A n is S f (fun i _ => hstable i) (fun i _ => hchar i)

end Erdos3.CircleFourier

end

section

namespace Erdos3.NilpotentLieBCHGroup

open CircleFourier
open scoped NNReal

variable {L ι : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_prescribed_central_projection
    (Γ T : Subgroup (NilpotentLieBCHGroup L s hnil))
    [PseudoMetricSpace (NilpotentLieBCHGroup L s hnil ⧸ Γ)]
    (hT : ∀ z ∈ T, ∀ v : L, ⁅z.coord, v⁆ = 0)
    (u : ι → L) (hline : ∀ i r, realBCHLine (hnil := hnil) (u i) r ∈ T)
    (hspan : ∀ z ∈ T, z.coord ∈ Submodule.span ℝ (Set.range u))
    (A : ι → IsometricCircleAction (NilpotentLieBCHGroup L s hnil ⧸ Γ))
    (hcomm : ∀ i j, (A i).Commutes (A j))
    (hact : ∀ i (r : ℝ) x, (A i).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := hnil) (u i) r • x)
    (η : L →ₗ[ℝ] ℝ) (f : NilpotentLieBCHGroup L s hnil ⧸ Γ → ℂ)
    (hseed : ∀ z ∈ T, f (QuotientGroup.mk z) = logCharacter η z)
    {K : ℝ≥0} {B : ℝ} (hf : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ B) :
    ∃ g : NilpotentLieBCHGroup L s hnil ⧸ Γ → ℂ,
      LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ B) ∧
      (∀ z ∈ T, ∀ x, g (z • x) = logCharacter η z * g x) ∧
      ∀ z ∈ T, g (QuotientGroup.mk z) = logCharacter η z := by
  classical
  have hperiod (i) : (QuotientGroup.mk (realBCHLine (hnil := hnil) (u i) 1) : _ ⧸ Γ) =
      QuotientGroup.mk (1 : NilpotentLieBCHGroup L s hnil) := by
    have h := hact i 1 (QuotientGroup.mk (1 : NilpotentLieBCHGroup L s hnil))
    simpa only [AddCircle.coe_period, (A i).zero_act, MulAction.Quotient.smul_mk,
      smul_eq_mul, mul_one] using h.symm
  have hint (i) : ∃ n : ℤ, η (u i) = n := by
    have he : character (η (u i) : CircleFourier.Circle) = 1 := by
      calc
        _ = f (QuotientGroup.mk (realBCHLine (hnil := hnil) (u i) 1)) := by
          rw [hseed _ (hline i 1)]
          simp only [logCharacter, realBCHLine, one_smul]
        _ = f (QuotientGroup.mk (1 : NilpotentLieBCHGroup L s hnil)) := congrArg f (hperiod i)
        _ = 1 := by rw [hseed _ T.one_mem]; simp only [logCharacter, coord_one, map_zero,
          AddCircle.coe_zero, character_zero]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp ((character_eq_one_iff _).mp he)
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩
  choose n hn using hint
  have hlinechar (i r) : logCharacter η (realBCHLine (hnil := hnil) (u i) r) =
      character (n i • (r : CircleFourier.Circle)) := by
    simp only [logCharacter, realBCHLine, map_smul, smul_eq_mul, hn, ← AddCircle.coe_zsmul,
      zsmul_eq_mul, mul_comm]
  let S : Set (NilpotentLieBCHGroup L s hnil ⧸ Γ) := Set.range (fun z : T => QuotientGroup.mk z.val)
  have hstable : ∀ i t x, x ∈ S → (A i).act t x ∈ S := by
    intro i t x hx
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨z, rfl⟩ := hx
    rw [hact, MulAction.Quotient.smul_mk, smul_eq_mul]
    exact ⟨⟨realBCHLine (u i) r * z.val, T.mul_mem (hline i r) z.property⟩, rfl⟩
  have hchar : ∀ i t x, x ∈ S → f ((A i).act t x) = character (n i • t) * f x := by
    intro i t x hx
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨z, rfl⟩ := hx
    rw [hact, MulAction.Quotient.smul_mk, smul_eq_mul,
      hseed _ (T.mul_mem (hline i r) z.property), hseed _ z.property,
      logCharacter_mul η _ _ (hT _ (hline i r) z.val.coord), hlinechar]
  obtain ⟨g, hg, hgb, hgchar, hgeq⟩ :=
    exists_prescribed_circle_projection A n hcomm S f hstable hchar hf hb
  refine ⟨g, hg, hgb, ?_, fun z hz => (hgeq _ ⟨⟨z, hz⟩, rfl⟩).trans (hseed z hz)⟩
  intro z hz x
  apply central_span_character u (fun i v => ?_) η g (fun i r y => ?_) (hspan z hz) x
  · simpa only [realBCHLine, one_smul] using hT _ (hline i 1) v
  · have h := hgchar i (r : CircleFourier.Circle) y
    rw [hact, ← hlinechar] at h
    simpa only [logCharacter, realBCHLine, map_smul, smul_eq_mul] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

theorem exists_native_prescribed_projection {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (f : D.Space → ℂ) {K : ℝ≥0} {B : ℝ}
    (hf : letI := D.metricSpace; LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ B)
    (hseed : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
      f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z) :
    ∃ g : D.Space → ℂ, (letI := D.metricSpace; LipschitzWith K g) ∧
      (∀ x, ‖g x‖ ≤ B) ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
        g (z • x) = logCharacter (realifyFunctional η) z * g x) ∧
      g (QuotientGroup.mk (1 : D.RealGroup)) = 1 := by
  let := D.metricSpace
  obtain ⟨b, w, N, hlayers, _, _, hN, _, _, _, A, hcomm, _, hact⟩ :=
    D.exists_controlled_central_actions hp hD
  let S : Set (Fin (finrank ℚ L)) := {j | s ≤ w j}
  let u (j : S) := (N : ℝ) • b.baseChange ℝ j
  have hbReal (j : S) : b.baseChange ℝ j ∈ D.filtration.realLayer s := by
    rw [Basis.baseChange_apply]
    change rationalLieInclusion (b j) ∈ D.filtration.realLayer s
    apply D.filtration.rational_inclusion_mem_realLayer
    rw [hlayers s]
    exact Submodule.subset_span ⟨j, j.property, rfl⟩
  have hline (j : S) (r : ℝ) : realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (u j) r ∈ D.filtration.realification.subgroup s := by
    change r • ((N : ℝ) • b.baseChange ℝ j) ∈ D.filtration.realLayer s
    exact (D.filtration.realLayer s).smul_mem r ((D.filtration.realLayer s).smul_mem _ (hbReal j))
  obtain ⟨g, hg, hgb, hgvert, hgeq⟩ := exists_prescribed_central_projection
    D.realLattice (D.filtration.realification.subgroup s)
    (fun z hz v => D.filtration.realification.top_layer_central hz v) u hline
    (fun z hz => D.filtration.realLayer_le_span_scaled_basis b s S (hlayers s) N hN hz)
    A hcomm hact (realifyFunctional η) f hseed hf hb
  refine ⟨g, hg, hgb, hgvert, ?_⟩
  have h := hgeq 1 (D.filtration.realification.subgroup s).one_mem
  simpa only [logCharacter, coord_one, map_zero, AddCircle.coe_zero, CircleFourier.character_zero] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


