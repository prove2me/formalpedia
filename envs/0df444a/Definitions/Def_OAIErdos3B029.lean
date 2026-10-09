-- Prove2me | Definitions.Def_OAIErdos3B029
-- name    : OAIErdos3B029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T17:55:49.622497+00:00
-- url     : https://prove2.me/theorems/b2866568-0243-4832-892b-002def82262b
-- title:
--   OpenAI Erdős-3 split, definitions bundle 30 of 106
-- statement:
--   Definitions bundle 30 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B028`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 30 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.ordinary_top_eq`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedLiePermute`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedLiePermute_mul`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedLiePermute_one`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedLiePermute_ordinary_top`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedLiePermute_top`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedTopCoefficient`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedTopCoefficient_apply`, `OAI.Erdos3.MultidegreeLieFiltration.restrictBound`, `OAI.Erdos3.MultidegreeLieFiltration.restrictBoundRealOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.weightedLayer_eq_finite`, `OAI.Erdos3.NativeTwoVariableSplit.recOn`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_tangent`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_central_character_extension`, `OAI.Erdos3.NilpotentLieFiltration.FilteredFirstJet`, `OAI.Erdos3.NilpotentLieFiltration.adaptedDirectionalDerivative`, `OAI.Erdos3.NilpotentLieFiltration.adaptedDirectionalDerivative_coe`, `OAI.Erdos3.NilpotentLieFiltration.adaptedDirectionalDerivative_lie`, `OAI.Erdos3.NilpotentLieFiltration.adaptedDirectionalDerivative_mem_shifted`, `OAI.Erdos3.NilpotentLieFiltration.adaptedDirectionalTangent`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLogDerivative`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLogDerivativeLinear`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLogDerivativeLinear_apply`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLogDerivative_constant`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLogDerivative_constant_unit`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLogDerivative_mul`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialJet`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialJetHom`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialJetHom_apply`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialJetLie`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialJet_base`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialJet_baseHom`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialJet_tangent`, `OAI.Erdos3.NilpotentLieFiltration.constantPolynomialOrbit`, `OAI.Erdos3.NilpotentLieFiltration.directionalDerivative_mem_next`, `OAI.Erdos3.NilpotentLieFiltration.directionalDerivative_mem_shifted`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_sorted_adapted_basis_logHeight`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJetConstant`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJetConstant_map`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJetMap`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJetMap_eq_iff`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJetMap_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJetMap_surjective`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJetSymbol`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJetSymbol_map`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJet_lowerCentralSeries_eq_bot`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJet_normalizedRelativeLog`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJet_normalizedShift`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJet_translate`, `OAI.Erdos3.NilpotentLieFiltration.gradedPieceProjection_lie`, `OAI.Erdos3.NilpotentLieFiltration.normalizePolynomialOrbit`, `OAI.Erdos3.NilpotentLieFiltration.normalizePolynomialOrbit_eval`, `OAI.Erdos3.NilpotentLieFiltration.normalizePolynomialOrbit_zero`, `OAI.Erdos3.NilpotentLieFiltration.normalizedRelativeLog`, `OAI.Erdos3.NilpotentLieFiltration.normalizedShiftAdapted`, `OAI.Erdos3.NilpotentLieFiltration.orderedPolynomialPatch`, `OAI.Erdos3.NilpotentLieFiltration.orderedPolynomialSlots`, `OAI.Erdos3.NilpotentLieFiltration.orderedSlotFactor`, `OAI.Erdos3.NilpotentLieFiltration.orderedSlotOrbit`, `OAI.Erdos3.NilpotentLieFiltration.piLayerEquiv`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitEval_constant`, `OAI.Erdos3.NilpotentLieFiltration.realCoordinatePolynomialOrbit`, `OAI.Erdos3.NilpotentLieFiltration.realCoordinatePolynomialOrbit_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realCoordinatePolynomialOrbit_eval_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.realCoordinatePolynomialOrbit_log`, `OAI.Erdos3.NilpotentLieFiltration.realExtendedSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_lift`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolLift`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolMap_apply`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolMap_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolMap_representative`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolMap_surjective`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_ofCoordinates_top`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_realAdaptedPolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_ofCoordinates`, `OAI.Erdos3.NilpotentLieFiltration.real_adapted_coordinate_degree`, `OAI.Erdos3.NilpotentLieFiltration.real_ofCoordinates_adapted`, `OAI.Erdos3.NilpotentLieFiltration.real_scaled_adapted_basis_mem`, `OAI.Erdos3.NilpotentLieFiltration.relativeSquareSymbolMap_range`, `OAI.Erdos3.NilpotentLieFiltration.relativeSquareSymbol_lie_eq_zero`, `OAI.Erdos3.NilpotentLieFiltration.shiftedGradedPolynomial_directionalDerivative`, `OAI.Erdos3.NilpotentLieFiltration.shiftedGradedPolynomial_lie`, `OAI.Erdos3.NilpotentLieFiltration.squareDiagonalSymbolHom`, `OAI.Erdos3.NilpotentLieFiltration.squareRelativeGroupPart`, `OAI.Erdos3.NilpotentLieFiltration.squareRelativeGroupPart_projection`, `OAI.Erdos3.NilpotentLieFiltration.squareSndSymbolHom`, `OAI.Erdos3.NilpotentLieFiltration.squareSndSymbolHom_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.squareSndSymbolKernel_lie_eq_zero`, `OAI.Erdos3.NilpotentLieFiltration.squareSndSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.squareSndSymbolMap_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.squareSndSymbolMap_map_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.squareSndSymbolMap_relative`, `OAI.Erdos3.NilpotentLieFiltration.squareSndSymbolMap_symbol`, `OAI.Erdos3.NilpotentLieFiltration.symbolFirstDerivative`, `OAI.Erdos3.NilpotentLieFiltration.symbolFirstDerivative_map`, `OAI.Erdos3.NilpotentLieFiltration.taylorRemainder_mem_shifted`, `OAI.Erdos3.PolynomialPatch.shearKernel`, `OAI.Erdos3.PolynomialPatch.shearObservable`, `OAI.Erdos3.PolynomialPatch.shearOrbit`, `OAI.Erdos3.PolynomialSlots.shearCoordinatePolynomial`, `OAI.Erdos3.PolynomialSlots.shearCoordinatePolynomial_degree`, `OAI.Erdos3.PolynomialSlots.shearCoordinatePolynomial_eval`, `OAI.Erdos3.PolynomialSlots.shearGroupLift`, `OAI.Erdos3.PolynomialSlots.shearGroupLift_coordinate`, `OAI.Erdos3.PolynomialSlots.shearLogPolynomial`, `OAI.Erdos3.PolynomialSlots.shearLogPolynomial_adapted`, `OAI.Erdos3.PolynomialSlots.shearLogPolynomial_coordinate`, `OAI.Erdos3.PolynomialSlots.shearLogPolynomial_eval`, `OAI.Erdos3.PolynomialSlots.shearPolynomialOrbit`, `OAI.Erdos3.PolynomialSlots.shearPolynomialOrbit_realEval`, `OAI.Erdos3.RationalFilteredNilmanifold`, `OAI.Erdos3.RationalFilteredNilmanifold.GeometryComplexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.GeometryComplexityLE.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.ComplexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.ComplexityLE.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_layer_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_ordinary_layer_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.orbitToOrdinary`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.orbitToOrdinary_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.realSubgroup`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.realSubgroup_top`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.rec`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.restrictBound`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.restrictBound_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.weightedLayer_span`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.ComplexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.ComplexityLE.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.casesOn`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.const`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.evalCyclic`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_const`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_step_zero`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.norm_evalCyclic_le`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.norm_eval_le`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.normalizeBasepoint`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.normalizeBasepoint_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.normalizeBasepoint_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.normalizeBasepoint_zero`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.observable_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.RealGroup`, `OAI.Erdos3.RationalFilteredNilmanifold.Space`, `OAI.Erdos3.RationalFilteredNilmanifold.dropTop`, `OAI.Erdos3.RationalFilteredNilmanifold.dropTop_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.dropTop_lattice_back`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_central_seed`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_complex_reconstruction`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_rational_representatives`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_positive_layer_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.metricSpace`, `OAI.Erdos3.RationalFilteredNilmanifold.pi`, `OAI.Erdos3.RationalFilteredNilmanifold.productFinBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.productLayerBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.productLayerFinBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.product_inner_grid`, `OAI.Erdos3.RationalFilteredNilmanifold.product_outer_grid`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStep`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStep_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStep_lattice_back`, `OAI.Erdos3.RationalFilteredNilmanifold.raisedLayerBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.raisedLayerBasis_of_lt`, `OAI.Erdos3.RationalFilteredNilmanifold.realLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.realLattice_closed_discrete`, `OAI.Erdos3.RationalHeightLE.pow`, `OAI.Erdos3.ReplicatedIndex`, `OAI.Erdos3.ReplicatedPermutation`, `OAI.Erdos3.VectorPolynomial.coefficients_directionalDerivative`, `OAI.Erdos3.VectorPolynomial.coefficients_pderiv`, `OAI.Erdos3.VectorPolynomial.coefficients_taylorRemainder`, `OAI.Erdos3.VectorPolynomial.coefficients_taylorRemainder_monomial`, `OAI.Erdos3.VectorPolynomial.taylorRemainder`, `OAI.Erdos3.VectorPolynomial.taylorRemainder_apply`, `OAI.Erdos3.aeval_eq_of_weightedSupportLT`, `OAI.Erdos3.basisFrequency`, `OAI.Erdos3.basisFrequency_apply`, `OAI.Erdos3.basisFrequency_basis`, `OAI.Erdos3.basis_reindex_equivFun_symm`, `OAI.Erdos3.basis_reindex_span_weights`, `OAI.Erdos3.bchSubgroupCoordinates_reindex`, `OAI.Erdos3.bchSubgroup_inner_grid_reindex`, `OAI.Erdos3.bchSubgroup_outer_grid_reindex`, `OAI.Erdos3.boundedRationalCandidates`, `OAI.Erdos3.boundedRationalCandidates_card`, `OAI.Erdos3.ceil_exp_le_exp_add_one`, `OAI.Erdos3.ceil_exp_power_le_exp`, `OAI.Erdos3.detectedTranslationSeparation_budget`, `OAI.Erdos3.exists_bounded_normalized_square`, `OAI.Erdos3.finite_card_bounded_height_arrays`, `OAI.Erdos3.integerCoefficientPolynomials_aeval`, `OAI.Erdos3.integerTupleRatCast_injective`, `OAI.Erdos3.integerWeightedLoweringPoint`, `OAI.Erdos3.integerWeightedLoweringPointEquiv`, `OAI.Erdos3.integerWeightedLoweringPointEquiv_cast`, `OAI.Erdos3.integerWeightedLoweringPoint_cast`, `OAI.Erdos3.integerWeightedLoweringPoint_inv`, `OAI.Erdos3.le_squarefreeInputBudget`, `OAI.Erdos3.lieStructureConstants_reindex`, `OAI.Erdos3.linearMap_coordinate_logHeight`, `OAI.Erdos3.mem_boundedRationalCandidates`, `OAI.Erdos3.one_le_ceil_exp`, `OAI.Erdos3.polynomialPointAction`, `OAI.Erdos3.polynomialPointEquiv`, `OAI.Erdos3.polynomialShearBracketCoefficient`, `OAI.Erdos3.polynomialShearBracketCoefficient_natAbs_le`, `OAI.Erdos3.polynomialShearIndexOrder`, `OAI.Erdos3.polynomialShearIndex_card_le`, `OAI.Erdos3.polynomialShearLattice`, `OAI.Erdos3.polynomialShearLattice_inner_grid`, `OAI.Erdos3.polynomialShearLattice_outer_grid`, `OAI.Erdos3.polynomialShearMonomial_bracket_X`, `OAI.Erdos3.polynomialShearMonomial_monomial`, `OAI.Erdos3.polynomialShearMonomial_pderiv`, `OAI.Erdos3.polynomialShearOrbitSum`, `OAI.Erdos3.polynomialShearOrbitSum_lattice`, `OAI.Erdos3.polynomialShearOrderedBasis`, `OAI.Erdos3.polynomialShearOrderedBasis_inner_grid`, `OAI.Erdos3.polynomialShearOrderedBasis_layers`, `OAI.Erdos3.polynomialShearOrderedBasis_outer_grid`, `OAI.Erdos3.polynomialShearOrderedBasis_structure_height`, `OAI.Erdos3.polynomialShearOrderedWeight`, `OAI.Erdos3.polynomialShearQuotientSum`, `OAI.Erdos3.polynomialShearRealAutEquiv_symm_coord`, `OAI.Erdos3.polynomialShearRealLattice`, `OAI.Erdos3.polynomialShearRealLattice_closed_discrete`, `OAI.Erdos3.polynomialShearRealLattice_integer_permutation`, `OAI.Erdos3.polynomialShearRealPointAction`, `OAI.Erdos3.polynomialShearRealPointAction_rational`, `OAI.Erdos3.polynomialShearRealificationEquiv_repr`, `OAI.Erdos3.polynomialShear_denominatorGrid_iff`, `OAI.Erdos3.polynomialShear_integralVector_iff`, `OAI.Erdos3.polynomialShear_integral_iff`, `OAI.Erdos3.polynomialShear_scaledGrid_normalize`, `OAI.Erdos3.polynomialShear_structureConstants`, `OAI.Erdos3.polynomialShear_structureConstants_height`, `OAI.Erdos3.polynomialSubstitutionPoint`, `OAI.Erdos3.polynomialSubstitutionPoint_aeval`, `OAI.Erdos3.polynomial_map_aeval`, `OAI.Erdos3.rationalHeightLE_ceil_exp`, `OAI.Erdos3.rationalLogHeight`, `OAI.Erdos3.rationalLogHeight_le_iff`, `OAI.Erdos3.rationalLogHeight_le_of_height`, `OAI.Erdos3.rationalLogHeight_nonneg`, `OAI.Erdos3.rational_functional_value_logHeight`, `OAI.Erdos3.realificationQuotientChartedSpace`, `OAI.Erdos3.realifyFunctional`, `OAI.Erdos3.realifyFunctional_tmul`, `OAI.Erdos3.realify_basisFrequency_direction`, `OAI.Erdos3.replicatedIndex_card`, `OAI.Erdos3.replicatedPermutation`, `OAI.Erdos3.replicatedPermutationFintype`, `OAI.Erdos3.replicatedPermutation_block`, `OAI.Erdos3.replicatedPermutation_card_le`, `OAI.Erdos3.replicatedPermutation_injective`, `OAI.Erdos3.replicatedPermutation_mul`, `OAI.Erdos3.replicatedPermutation_one`, `OAI.Erdos3.replicated_blockDegree_apply`, `OAI.Erdos3.replicated_blockDegree_full`, `OAI.Erdos3.replicated_blockDegree_le`, `OAI.Erdos3.squarefreeBracketHeight_le_exp`, `OAI.Erdos3.squarefreeInputBudget`, `OAI.Erdos3.squarefreeInputBudget_nonneg`, `OAI.Erdos3.squarefreeStructureHeight_ceil_exp`, `OAI.Erdos3.squarefreeStructureHeight_le_exp`, `OAI.Erdos3.stepOne_denominator_budget`, `OAI.Erdos3.stepOne_kernel_height_budget`, `OAI.Erdos3.stepOne_linear_budget`, `OAI.Erdos3.stepOne_slow_budget`, `OAI.Erdos3.weightedLoweringPointAction`, `OAI.Erdos3.weightedLoweringSubstitution_difference`, `OAI.Erdos3.weightedLoweringSubstitution_prefix`, `_private.Polynomial.RealCoordinatePolynomialSymbol.0.OAI.Erdos3.NilpotentLieFiltration.repr_coefficients_ofCoordinates`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B093

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OrbitBasepointNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def constantPolynomialOrbit (a : F.Group) : F.PolynomialOrbit w :=
  F.adaptedBCHToOrbit w (F.adaptedConstantGroupHom w a)

theorem polynomialOrbitEval_constant (a : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval w x (F.constantPolynomialOrbit w a) = a := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ)) (monomial 0 a.coord) = a.coord
  rw [eval_monomial, Finsupp.prod_zero_index, one_smul]

noncomputable def normalizePolynomialOrbit (g : F.PolynomialOrbit w) (a γ : F.Group) :
    F.PolynomialOrbit w :=
  F.constantPolynomialOrbit w a⁻¹ * g * F.constantPolynomialOrbit w γ⁻¹

theorem normalizePolynomialOrbit_eval (g : F.PolynomialOrbit w) (a γ : F.Group)
    (x : σ → ℤ) :
    F.polynomialOrbitEval w x (F.normalizePolynomialOrbit w g a γ) =
      a⁻¹ * F.polynomialOrbitEval w x g * γ⁻¹ := by
  simp only [normalizePolynomialOrbit, map_mul, polynomialOrbitEval_constant]

theorem normalizePolynomialOrbit_zero (g : F.PolynomialOrbit w) (a γ : F.Group)
    (hg : F.polynomialOrbitEval w 0 g = a * γ) :
    F.polynomialOrbitEval w 0 (F.normalizePolynomialOrbit w g a γ) = 1 := by
  rw [normalizePolynomialOrbit_eval, hg]
  simp

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem basis_reindex_equivFun_symm (b : Basis ι ℚ L) (e : ι ≃ κ) (x : κ → ℚ) :
    (b.reindex e).equivFun.symm x = b.equivFun.symm (fun i => x (e i)) := by
  apply b.equivFun.injective
  funext i
  rw [LinearEquiv.apply_symm_apply]
  have h := congrFun ((b.reindex e).equivFun.apply_symm_apply x) (e i)
  simpa only [Basis.equivFun_apply, Basis.repr_reindex_apply,
    Equiv.symm_apply_apply] using h

theorem bchSubgroupCoordinates_reindex (b : Basis ι ℚ L) (e : ι ≃ κ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (x : κ → ℚ) :
    x ∈ bchSubgroupCoordinates (b.reindex e) Γ ↔
      (fun i => x (e i)) ∈ bchSubgroupCoordinates b Γ := by
  unfold bchSubgroupCoordinates
  simp only [Set.mem_ofPred_eq, basis_reindex_equivFun_symm]

theorem bchSubgroup_inner_grid_reindex (b : Basis ι ℚ L) (e : ι ≃ κ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {N : ℕ}
    (h : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) :
    scaledIntegerGrid N ⊆ bchSubgroupCoordinates (b.reindex e) Γ := by
  rintro x ⟨z, rfl⟩
  apply (bchSubgroupCoordinates_reindex b e Γ _).mpr
  exact h ⟨fun i => z (e i), rfl⟩

theorem bchSubgroup_outer_grid_reindex (b : Basis ι ℚ L) (e : ι ≃ κ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {N : ℕ}
    (h : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    bchSubgroupCoordinates (b.reindex e) Γ ⊆ denominatorGrid N := by
  intro x hx
  obtain ⟨z, hz⟩ := h ((bchSubgroupCoordinates_reindex b e Γ x).mp hx)
  refine ⟨fun i => z (e.symm i), fun i => ?_⟩
  simpa only [Pi.smul_apply, Equiv.apply_symm_apply] using hz (e.symm i)

omit [Fintype ι] [Fintype κ] in
theorem basis_reindex_span_weights (b : Basis ι ℚ L) (e : ι ≃ κ)
    (w : ι → ℕ) (j : ℕ) :
    Submodule.span ℚ ((b.reindex e) '' {i | j ≤ w (e.symm i)}) =
      Submodule.span ℚ (b '' {i | j ≤ w i}) := by
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.symm i, hi, (Basis.reindex_apply b e i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e i, ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hi
    · simp only [Basis.reindex_apply, Equiv.symm_apply_apply]

omit [Fintype ι] [Fintype κ] in
theorem lieStructureConstants_reindex (b : Basis ι ℚ L) (e : ι ≃ κ) (i j k : κ) :
    lieStructureConstants (b.reindex e) i j k =
      lieStructureConstants b (e.symm i) (e.symm j) (e.symm k) := by
  simp only [lieStructureConstants, Basis.reindex_apply, Basis.repr_reindex_apply]

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

local notation "G" => NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)

variable (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

@[instance_reducible]
noncomputable def realificationQuotientChartedSpace :
    ChartedSpace (ι → ℝ) (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) :=
  NilpotentLieBCHGroup.quotientChartedSpace (e.baseChange ℝ) (lieStructureConstants e)
    (fun i j k => (realLieBasis_structure e i j k).symm) hc
    (Γ.map NilpotentLieBCHGroup.realificationHom) l hl
    (NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter)

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s H₁ H₂ : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure RationalFilteredNilmanifold (s d : ℕ) where
  filtration : NilpotentLieFiltration L s
  basis : Basis (Fin d) ℚ L
  layerBasis : ∀ i : Fin (s + 1),
    Basis (Fin (Module.finrank ℚ (filtration.layer (i.val + 1)))) ℚ (filtration.layer (i.val + 1))
  lattice : Subgroup filtration.Group
  grid : ℕ
  grid_pos : 0 < grid
  inner_grid : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates basis lattice
  outer_grid : bchSubgroupCoordinates basis lattice ⊆ denominatorGrid grid

noncomputable def rationalLogHeight (q : ℚ) : ℝ :=
  Real.log (max (q.num.natAbs : ℝ) (q.den : ℝ))

namespace RationalFilteredNilmanifold

variable {L} {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

abbrev RealGroup := D.filtration.realification.Group

noncomputable def realLattice : Subgroup D.RealGroup :=
  D.lattice.map NilpotentLieBCHGroup.realificationHom

abbrev Space : Type _ := D.RealGroup ⧸ D.realLattice

def GeometryComplexityLE (p : ℝ) : Prop :=
  (d : ℝ) ≤ p ∧ (D.grid : ℝ) ≤ Real.exp p ∧
  (∀ i j k, rationalLogHeight (lieStructureConstants D.basis i j k) ≤ p) ∧
  (∀ i j k, rationalLogHeight (D.basis.repr (D.layerBasis i j) k) ≤ p)

theorem GeometryComplexityLE.mono {p q : ℝ} (hp : D.GeometryComplexityLE p) (hpq : p ≤ q) :
    D.GeometryComplexityLE q :=
  ⟨hp.1.trans hpq, hp.2.1.trans (Real.exp_le_exp.mpr hpq),
    fun i j k => (hp.2.2.1 i j k).trans hpq,
    fun i j k => (hp.2.2.2 i j k).trans hpq⟩

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

@[instance_reducible]
noncomputable def metricSpace : MetricSpace D.Space :=
  realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid

theorem realLattice_closed_discrete :
    IsClosed (D.realLattice : Set D.RealGroup) ∧ IsDiscrete (D.realLattice : Set D.RealGroup) :=
  NilpotentLieBCHGroup.realification_subgroup_closed_discrete
    D.basis D.lattice D.grid D.grid_pos D.outer_grid

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (hD : D.filtration.layer (s + 1) = ⊥)

noncomputable def dropTop : RationalFilteredNilmanifold L s d where
  filtration := D.filtration.dropTop hD
  basis := D.basis
  layerBasis i := D.layerBasis ⟨i.val, by omega⟩
  lattice := D.lattice.map (NilpotentLieBCHGroup.changeStep D.filtration.lowerCentralSeries_eq_bot
    (D.filtration.dropTop hD).lowerCentralSeries_eq_bot).toMonoidHom
  grid := D.grid
  grid_pos := D.grid_pos
  inner_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.inner_grid
  outer_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.outer_grid

theorem dropTop_geometry {p : ℝ} (hp : D.GeometryComplexityLE p) :
    (D.dropTop hD).GeometryComplexityLE p :=
  ⟨hp.1, hp.2.1, hp.2.2.1, fun i j k => hp.2.2.2 ⟨i.val, by omega⟩ j k⟩

theorem dropTop_lattice_back :
    (D.dropTop hD).lattice ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (hL := (D.filtration.dropTop hD).lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact hx

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

structure Niltest (w : σ → ℕ) where
  orbit : D.filtration.realification.PolynomialOrbit w
  observable : D.Space → ℂ
  normBound : ℝ≥0
  lipBound : ℝ≥0
  norm_le : ∀ x, ‖observable x‖ ≤ normBound
  lipschitz : letI := D.metricSpace; LipschitzWith lipBound observable

namespace Niltest

variable {D} {w : σ → ℕ}

noncomputable def const (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) (c : ℂ) :
    D.Niltest w where
  orbit := 1
  observable := fun _ => c
  normBound := ‖c‖₊
  lipBound := 0
  norm_le _ := le_rfl
  lipschitz := by
    let := D.metricSpace
    exact LipschitzWith.const c

noncomputable def eval (T : D.Niltest w) (x : σ → ℤ) : ℂ :=
  T.observable (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

@[simp] theorem eval_const (D : RationalFilteredNilmanifold L s d)
    (w : σ → ℕ) (c : ℂ) (x : σ → ℤ) : (const D w c).eval x = c := rfl

theorem norm_eval_le (T : D.Niltest w) (x : σ → ℤ) : ‖T.eval x‖ ≤ T.normBound :=
  T.norm_le _

noncomputable def evalCyclic (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) : ℂ :=
  T.eval (fun i => ((x i).val : ℤ))

theorem norm_evalCyclic_le (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    ‖T.evalCyclic N x‖ ≤ T.normBound := T.norm_eval_le _

def ComplexityLE (T : D.Niltest w) (p : ℝ) : Prop :=
  D.GeometryComplexityLE p ∧ Real.log (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) ≤ p

theorem ComplexityLE.mono {T : D.Niltest w} {p q : ℝ}
    (hp : T.ComplexityLE p) (hpq : p ≤ q) : T.ComplexityLE q :=
  ⟨GeometryComplexityLE.mono D hp.1 hpq, hp.2.trans hpq⟩

theorem observable_budget {T : D.Niltest w} {p : ℝ} (hp : T.ComplexityLE p) :
    2 + (T.normBound : ℝ) + (T.lipBound : ℝ) ≤ Real.exp p := by
  have hpos : 0 < 2 + (T.normBound : ℝ) + (T.lipBound : ℝ) := by positivity
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hp.2

theorem eval_budget {T : D.Niltest w} {p : ℝ} (hp : T.ComplexityLE p) (x : σ → ℤ) :
    ‖T.eval x‖ ≤ Real.exp p := by
  have h := observable_budget hp
  have hn := T.norm_eval_le x
  have hl := T.lipBound.coe_nonneg
  linarith

theorem eval_step_zero (D : RationalFilteredNilmanifold L 0 d)
    (T : D.Niltest w) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk (1 : D.RealGroup)) := by
  unfold eval
  rw [NilpotentLieFiltration.polynomialOrbitEval_step_zero]

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

noncomputable def raisedLayerBasis (i : Fin (t + 1)) :
    Basis (Fin (Module.finrank ℚ ((D.filtration.raiseStep hst).layer (i.val + 1)))) ℚ
      ((D.filtration.raiseStep hst).layer (i.val + 1)) := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact if hi : i.val < s + 1 then D.layerBasis ⟨i.val, hi⟩ else
    Module.finBasis ℚ ((D.filtration.raiseStep hst).layer (i.val + 1))

theorem raisedLayerBasis_of_lt (i : Fin (t + 1)) (hi : i.val < s + 1) :
    D.raisedLayerBasis hst i = D.layerBasis ⟨i.val, hi⟩ := by
  simp [raisedLayerBasis, hi]
  rfl

noncomputable def raiseStep : RationalFilteredNilmanifold L t d where
  filtration := D.filtration.raiseStep hst
  basis := D.basis
  layerBasis := D.raisedLayerBasis hst
  lattice := D.lattice.map (NilpotentLieBCHGroup.changeStep D.filtration.lowerCentralSeries_eq_bot
    (D.filtration.raiseStep hst).lowerCentralSeries_eq_bot).toMonoidHom
  grid := D.grid
  grid_pos := D.grid_pos
  inner_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.inner_grid
  outer_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.outer_grid

theorem raiseStep_geometry {p : ℝ} (hD : D.GeometryComplexityLE p) :
    (D.raiseStep hst).GeometryComplexityLE p := by
  refine ⟨hD.1, hD.2.1, hD.2.2.1, ?_⟩
  intro i j k
  by_cases hi : i.val < s + 1
  · change rationalLogHeight (D.basis.repr (D.raisedLayerBasis hst i j) k) ≤ p
    rw [D.raisedLayerBasis_of_lt hst i hi]
    exact hD.2.2.2 ⟨i.val, hi⟩ j k
  · have hbot : D.filtration.layer (i.val + 1) = ⊥ :=
      D.filtration.layer_eq_bot_above_step (by omega)
    have hrank : Module.finrank ℚ ((D.filtration.raiseStep hst).layer (i.val + 1)) = 0 := by
      rw [NilpotentLieFiltration.raiseStep_layer, hbot]
      simp
    have hj := j.isLt
    change j.val < Module.finrank ℚ ((D.filtration.raiseStep hst).layer (i.val + 1)) at hj
    rw [hrank] at hj
    omega

theorem raiseStep_lattice_back :
    (D.raiseStep hst).lattice ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (hL := (D.filtration.raiseStep hst).lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact hx

end Erdos3.RationalFilteredNilmanifold

end

section

open Module
open scoped BigOperators

namespace Erdos3

namespace NilpotentLieFiltration

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

def piLayerEquiv (F : ∀ i, NilpotentLieFiltration (L i) s) (n : ℕ) :
    (∀ i, (F i).layer n) ≃ₗ[ℚ] (pi F).layer n where
  toFun x := ⟨fun i => x i, (mem_pi_layer F n _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, (mem_pi_layer F n _).mp x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def productFinBasis : Basis (Fin (Fintype.card (Σ i, Fin (d i)))) ℚ (∀ i, L i) :=
  (Pi.basis (fun i => (D i).basis)).reindex (Fintype.equivFin _)

noncomputable def productLayerBasis (j : Fin (s + 1)) :
    Basis (Σ i, Fin (finrank ℚ ((D i).filtration.layer (j.val + 1)))) ℚ
      ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1)) :=
  (Pi.basis (fun i => (D i).layerBasis j)).map
    (NilpotentLieFiltration.piLayerEquiv (fun i => (D i).filtration) (j.val + 1))

noncomputable def productLayerFinBasis (j : Fin (s + 1)) :
    Basis (Fin (finrank ℚ ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1)))) ℚ
      ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1)) :=
  (productLayerBasis D j).reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis (productLayerBasis D j)).symm)

theorem product_inner_grid : scaledIntegerGrid (∏ i, (D i).grid) ⊆
    bchSubgroupCoordinates (productFinBasis D)
      (piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)) := by
  classical
  apply bchSubgroup_inner_grid_reindex
  apply piBCHSubgroup_inner_grid
  intro i
  exact (scaledIntegerGrid_subset_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))).trans (D i).inner_grid

theorem product_outer_grid :
    bchSubgroupCoordinates (productFinBasis D)
      (piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)) ⊆
        denominatorGrid (∏ i, (D i).grid) := by
  classical
  apply bchSubgroup_outer_grid_reindex
  apply piBCHSubgroup_outer_grid
  intro i
  exact (D i).outer_grid.trans (denominatorGrid_subset_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

noncomputable def pi : RationalFilteredNilmanifold (∀ i, L i) s (Fintype.card (Σ i, Fin (d i))) where
  filtration := NilpotentLieFiltration.pi (fun i => (D i).filtration)
  basis := productFinBasis D
  layerBasis := productLayerFinBasis D
  lattice := piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)
  grid := ∏ i, (D i).grid
  grid_pos := Finset.prod_pos (fun i _ => (D i).grid_pos)
  inner_grid := product_inner_grid D
  outer_grid := product_outer_grid D

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def normalizeBasepoint (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x)) : D.Niltest w where
  orbit := D.filtration.realification.normalizePolynomialOrbit w T.orbit a γ
  observable := fun x => T.observable (a • x)
  normBound := T.normBound
  lipBound := T.lipBound * A
  norm_le x := T.norm_le (a • x)
  lipschitz := by
    let := D.metricSpace
    exact T.lipschitz.comp hA

theorem normalizeBasepoint_zero (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    (hg : D.filtration.realification.polynomialOrbitEval w 0 T.orbit = a * γ) :
    D.filtration.realification.polynomialOrbitEval w 0 (T.normalizeBasepoint a γ A hA).orbit = 1 :=
  D.filtration.realification.normalizePolynomialOrbit_zero w T.orbit a γ hg

theorem normalizeBasepoint_eval (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    (hγ : γ ∈ D.realLattice) (x : σ → ℤ) :
    (T.normalizeBasepoint a γ A hA).eval x = T.eval x := by
  change T.observable (a • QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w x
      (D.filtration.realification.normalizePolynomialOrbit w T.orbit a γ))) = _
  rw [NilpotentLieFiltration.normalizePolynomialOrbit_eval]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  exact congrArg T.observable (QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ))

theorem normalizeBasepoint_complexity (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    {p q : ℝ} (hT : T.ComplexityLE p) (hq : 0 ≤ q) (hbound : (A : ℝ) ≤ Real.exp q) :
    (T.normalizeBasepoint a γ A hA).ComplexityLE (p + q) := by
  refine ⟨hT.1.mono D (le_add_of_nonneg_right hq), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) + (T.lipBound : ℝ) * A) ≤ p + q
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have h1 : 1 ≤ Real.exp q := Real.one_le_exp hq
  calc
    _ ≤ (2 + (T.normBound : ℝ)) * Real.exp q + (T.lipBound : ℝ) * Real.exp q :=
      add_le_add (le_mul_of_one_le_right (by positivity) h1)
        (mul_le_mul_of_nonneg_left hbound T.lipBound.coe_nonneg)
    _ = (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) * Real.exp q := by ring
    _ ≤ Real.exp p * Real.exp q := mul_le_mul_of_nonneg_right (observable_budget hT) (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*}

abbrev ReplicatedIndex (bound : σ → ℕ) := Σ i, Fin (bound i)

theorem replicatedIndex_card [Fintype σ] (bound : σ → ℕ) :
    Fintype.card (ReplicatedIndex bound) = ∑ i, bound i := by
  simp only [ReplicatedIndex, Fintype.card_sigma, Fintype.card_fin]

def replicatedPermutation (bound : σ → ℕ) (e : ∀ i, Equiv.Perm (Fin (bound i))) :
    Equiv.Perm (ReplicatedIndex bound) := Equiv.sigmaCongrRight e

theorem replicatedPermutation_block (bound : σ → ℕ) (e : ∀ i, Equiv.Perm (Fin (bound i)))
    (j : ReplicatedIndex bound) : (replicatedPermutation bound e j).1 = j.1 := rfl

theorem replicated_blockDegree_apply [Fintype σ] (bound : σ → ℕ)
    (a : ReplicatedIndex bound →₀ ℕ) (i : σ) :
    blockDegree (fun j : ReplicatedIndex bound => j.1) a i = ∑ j : Fin (bound i), a ⟨i, j⟩ := by
  classical
  change (∑ j : ReplicatedIndex bound, if j.1 = i then a j else 0) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [hji, ite_false, Finset.sum_const_zero]
  · simp

theorem replicated_blockDegree_le [Fintype σ] (bound : σ → ℕ)
    (a : SquarefreeIndex (ReplicatedIndex bound)) :
    blockDegree (fun j : ReplicatedIndex bound => j.1) a.val ≤ bound := by
  intro i
  rw [replicated_blockDegree_apply]
  calc
    _ ≤ ∑ _j : Fin (bound i), 1 := Finset.sum_le_sum fun j _ => a.property ⟨i, j⟩
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} (bound : σ → ℕ)

abbrev ReplicatedPermutation := ∀ i, Equiv.Perm (Fin (bound i))

noncomputable instance replicatedPermutationFintype [Fintype σ] :
    Fintype (ReplicatedPermutation bound) := Fintype.ofFinite _

theorem replicatedPermutation_one :
    replicatedPermutation bound (1 : ReplicatedPermutation bound) = 1 := by
  apply Equiv.ext
  intro i
  cases i
  rfl

theorem replicatedPermutation_mul (e f : ReplicatedPermutation bound) :
    replicatedPermutation bound (e * f) = replicatedPermutation bound e * replicatedPermutation bound f := by
  apply Equiv.ext
  intro i
  cases i
  rfl

theorem replicatedPermutation_injective : Function.Injective (replicatedPermutation bound) := by
  intro e f h
  funext i
  apply Equiv.ext
  intro j
  have hh := congrArg (fun g : Equiv.Perm (ReplicatedIndex bound) => g ⟨i, j⟩) h
  change (⟨i, e i j⟩ : ReplicatedIndex bound) = ⟨i, f i j⟩ at hh
  exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2

theorem replicatedPermutation_card_le [Fintype σ] :
    Fintype.card (ReplicatedPermutation bound) ≤ (∑ i, bound i).factorial := by
  classical
  have h := Fintype.card_le_of_injective _ (replicatedPermutation_injective bound)
  simpa only [Fintype.card_perm, replicatedIndex_card] using h

end Erdos3

end

section

namespace Erdos3

theorem replicated_blockDegree_full {σ : Type*} [Fintype σ] (bound : σ → ℕ) :
    blockDegree (fun j : ReplicatedIndex bound => j.1)
      (SquarefreeIndex.full (ReplicatedIndex bound)).val = bound := by
  ext i
  rw [replicated_blockDegree_apply]
  simp only [SquarefreeIndex.full_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one]

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def replicatedTopCoefficient :
    F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) →ₗ[ℚ] F.layer bound where
  toFun x := ⟨squarefreePolynomialEquiv x.val (SquarefreeIndex.full (ReplicatedIndex bound)), by
    have h := (x.property (SquarefreeIndex.full (ReplicatedIndex bound))).1
    simpa only [replicated_blockDegree_full] using h⟩
  map_add' x y := by
    apply Subtype.ext
    exact congrFun (map_add squarefreePolynomialEquiv x.val y.val) _
  map_smul' r x := by
    apply Subtype.ext
    exact congrFun (map_smul squarefreePolynomialEquiv r x.val) _

theorem replicatedTopCoefficient_apply
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    (F.replicatedTopCoefficient x).val =
      squarefreePolynomialEquiv x.val (SquarefreeIndex.full (ReplicatedIndex bound)) := rfl

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure MultidegreeStructure (D : RationalFilteredNilmanifold L s d) (bound : σ → ℕ) where
  filtration : MultidegreeLieFiltration σ L s bound
  ordinary : filtration.ordinary = D.filtration
  basis : ∀ a : ∀ i, Fin (bound i + 1),
    Basis (Fin (finrank ℚ (filtration.layer (fun i => (a i).val)))) ℚ
      (filtration.layer (fun i => (a i).val))

namespace MultidegreeStructure

variable {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

def ComplexityLE (p : ℝ) : Prop := D.GeometryComplexityLE p ∧
  ∀ a j k, rationalLogHeight (D.basis.repr (M.basis a j : L) k) ≤ p

theorem ComplexityLE.mono {p q : ℝ} (hM : M.ComplexityLE p) (hpq : p ≤ q) : M.ComplexityLE q :=
  ⟨hM.1.mono D hpq, fun a j k => (hM.2 a j k).trans hpq⟩

noncomputable def realSubgroup (a : σ → ℕ) : Subgroup D.RealGroup := M.filtration.realification.subgroup a

noncomputable def orbitToOrdinary : M.filtration.realification.PolynomialOrbit →*
    D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) := by
  have h : M.filtration.realification.ordinary = D.filtration.realification := by
    change M.filtration.ordinary.realification = D.filtration.realification
    rw [M.ordinary]
  exact (M.filtration.realification.ordinary.orbitEquivOfEq h (fun _ : σ => 1)).toMonoidHom.comp
    M.filtration.realification.toOrdinaryOrbit

theorem orbitToOrdinary_eval (g : M.filtration.realification.PolynomialOrbit) (x : σ → ℤ) :
    D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x (M.orbitToOrdinary g) =
      M.filtration.realification.polynomialOrbitEval x g := by
  have h : M.filtration.realification.ordinary = D.filtration.realification := by
    change M.filtration.ordinary.realification = D.filtration.realification
    rw [M.ordinary]
  change D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x
    (M.filtration.realification.ordinary.orbitEquivOfEq h (fun _ : σ => 1)
      (M.filtration.realification.toOrdinaryOrbit g)) = _
  rw [NilpotentLieFiltration.orbitEquivOfEq_eval,
    MultidegreeLieFiltration.toOrdinaryOrbit_eval]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end MultidegreeStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace MultidegreeLieFiltration

theorem ordinary_top_eq {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) :
    F.ordinary.layer (∑ i, bound i) = F.layer bound := by
  classical
  apply le_antisymm
  · rw [F.degree_eq]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    by_cases hle : a ≤ bound
    · have hsum : (∑ i, a i) = ∑ i, bound i :=
        le_antisymm (Finset.sum_le_sum (fun i _ => hle i)) ha
      have heq : a = bound := funext (fun i =>
        (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum i (Finset.mem_univ i))
      rw [heq]
    · rw [F.terminal a hle]
      exact bot_le
  · exact F.layer_le_ordinary bound

end MultidegreeLieFiltration

namespace RationalFilteredNilmanifold.MultidegreeStructure

theorem realSubgroup_top {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
    (M : D.MultidegreeStructure bound) :
    M.realSubgroup bound = D.filtration.realification.subgroup (∑ i, bound i) := by
  ext x
  change x.coord ∈ (M.filtration.layer bound).baseChange ℝ ↔
    x.coord ∈ (D.filtration.layer (∑ i, bound i)).baseChange ℝ
  rw [← M.ordinary, M.filtration.ordinary_top_eq]

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def restrictBound (bound' : σ → ℕ)
    (hzero : ∀ a, ¬a ≤ bound' → F.layer a = ⊥) :
    MultidegreeLieFiltration σ L s bound' where
  ordinary := F.ordinary
  layer := F.layer
  antitone := F.antitone
  zero_eq_top := F.zero_eq_top
  lie_mem := F.lie_mem
  terminal := hzero
  degree_eq := F.degree_eq

noncomputable def restrictBoundRealOrbit (bound' : σ → ℕ)
    (hzero : ∀ a, ¬a ≤ bound' → F.layer a = ⊥)
    (g : F.realification.PolynomialOrbit) :
    (F.restrictBound bound' hzero).realification.PolynomialOrbit := g

end MultidegreeLieFiltration

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def restrictBound (bound' : σ → ℕ) (hbound : bound' ≤ bound)
    (hzero : ∀ a, ¬a ≤ bound' → M.filtration.layer a = ⊥) :
    D.MultidegreeStructure bound' where
  filtration := M.filtration.restrictBound bound' hzero
  ordinary := M.ordinary
  basis a := M.basis (fun i => ⟨(a i).val, lt_of_lt_of_le (a i).isLt (Nat.add_le_add_right (hbound i) 1)⟩)

theorem restrictBound_complexity (bound' : σ → ℕ) (hbound : bound' ≤ bound)
    (hzero : ∀ a, ¬a ≤ bound' → M.filtration.layer a = ⊥)
    {p : ℝ} (hM : M.ComplexityLE p) :
    (M.restrictBound bound' hbound hzero).ComplexityLE p :=
  ⟨hM.1, fun a => hM.2 (fun i =>
    ⟨(a i).val, lt_of_lt_of_le (a i).isLt (Nat.add_le_add_right (hbound i) 1)⟩)⟩

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedLayer_eq_finite (c : σ → ℕ) (n : ℕ) :
    F.weightedLayer c n =
      ⨆ a : {a : ∀ i, Fin (bound i + 1) // n ≤ multidegreeWeight c (fun i => (a i).val)},
        F.layerIdeal (fun i => (a.val i).val) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro a
    by_cases ha : a.val ≤ bound
    · let b : ∀ i, Fin (bound i + 1) := fun i => ⟨a.val i, Nat.lt_succ_of_le (ha i)⟩
      exact le_iSup_of_le ⟨b, a.property⟩ le_rfl
    · intro x hx
      have h : x = 0 := by
        have hx' : x ∈ F.layer a.val := hx
        simpa only [F.terminal a.val ha, Submodule.mem_bot] using hx'
      rw [h]
      exact LieSubmodule.zero_mem _
  · apply iSup_le
    intro a
    exact F.layer_le_weightedLayer c (fun i => (a.val i).val) n a.property

end Erdos3.MultidegreeLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem weightedLayer_span (c : σ → ℕ) (n : ℕ) :
    (M.filtration.weightedLayer c n).toSubmodule = Submodule.span ℚ
      (Set.range (fun a : Σ a : {a : ∀ i, Fin (bound i + 1) //
          n ≤ multidegreeWeight c (fun i => (a i).val)},
          Fin (finrank ℚ (M.filtration.layer (fun i => (a.val i).val))) =>
        (M.basis a.1.val a.2 : L))) := by
  rw [M.filtration.weightedLayer_eq_finite]
  simp only [LieSubmodule.iSup_toSubmodule]
  apply le_antisymm
  · apply iSup_le
    intro a
    change M.filtration.layer (fun i => (a.val i).val) ≤ _
    rw [← span_submodule_basis _ (M.basis a.val)]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨a, j⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨a, j⟩, rfl⟩
    exact Submodule.mem_iSup_of_mem a (M.basis a.val j).property

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeTwoVariableSplit (s d : ℕ) (p epsilon : ℝ)
    (f : (Fin 2 → ℤ) → ℂ) where
  count : ℕ
  count_pos : 0 < count
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Bool → Type
  [lie : ∀ b, LieRing (L b)]
  [algebra : ∀ b, LieAlgebra ℚ (L b)]
  dim : Bool → ℕ
  [topology : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] L b)]
  [topologicalAdd : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] L b)]
  [continuousSMul : ∀ b, ContinuousSMul ℝ (ℝ ⊗[ℚ] L b)]
  [hausdorff : ∀ b, T2Space (ℝ ⊗[ℚ] L b)]
  model : ∀ b, RationalFilteredNilmanifold (L b) (∑ _ : Fin 2, s) (dim b)
  multi : ∀ b, (model b).MultidegreeStructure (totalDegreeSplitBound s b)
  complexity : ∀ b, (multi b).ComplexityLE p
  dimension_bound : ∀ b, dim b ≤ 2 ^ (2 * s) * d
  orbit : ∀ b, (multi b).filtration.realification.PolynomialOrbit
  test : ∀ b, Fin count → (model b).Niltest (fun _ : Fin 2 => 1)
  test_norm : ∀ b j, (test b j).normBound ≤ 1
  test_complexity : ∀ b j, (test b j).ComplexityLE p
  test_orbit : ∀ b j, (test b j).orbit = (multi b).orbitToOrdinary (orbit b)
  approximation : ∀ x,
    ‖f x - ∑ j, (test false j).eval x * (test true j).eval x‖ ≤ epsilon

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def replicatedLiePermute (e : ReplicatedPermutation bound) :
    F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) ≃ₗ⁅ℚ⁆
      F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) :=
  F.squarefreeBlockPermute _ (replicatedPermutation bound e) (replicatedPermutation_block bound e)

theorem replicatedLiePermute_one (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedLiePermute 1 x = x := by
  unfold replicatedLiePermute
  simp only [replicatedPermutation_one]
  exact F.squarefreeBlockPermute_one _ x

theorem replicatedLiePermute_mul (e f : ReplicatedPermutation bound)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedLiePermute (e * f) x = F.replicatedLiePermute e (F.replicatedLiePermute f x) := by
  apply Subtype.ext
  change squarefreePermute (replicatedPermutation bound (e * f)) x.val =
    squarefreePermute (replicatedPermutation bound e)
      (squarefreePermute (replicatedPermutation bound f) x.val)
  rw [replicatedPermutation_mul, squarefreePermute_mul]

theorem replicatedLiePermute_top (e : ReplicatedPermutation bound)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
    (hx : x ∈ F.squarefreeMultidegreeLayer (fun j : ReplicatedIndex bound => j.1) (fun _ => 1)) :
    F.replicatedLiePermute e x = x :=
  F.squarefreeBlockPermute_eq_self_top _ _ _ x hx

theorem replicatedLiePermute_ordinary_top (e : ReplicatedPermutation bound)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
    (hx : x ∈ (F.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).layer
      (Fintype.card (ReplicatedIndex bound))) : F.replicatedLiePermute e x = x := by
  have htop := (F.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)).ordinary_top_eq
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at htop
  change (F.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).layer
    (Fintype.card (ReplicatedIndex bound)) =
      F.squarefreeMultidegreeLayer (fun j : ReplicatedIndex bound => j.1) (fun _ => 1) at htop
  apply F.replicatedLiePermute_top e x
  rw [← htop]
  exact hx

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3

theorem rationalLogHeight_le_iff (q : ℚ) (p : ℝ) :
    rationalLogHeight q ≤ p ↔
      (q.num.natAbs : ℝ) ≤ Real.exp p ∧ (q.den : ℝ) ≤ Real.exp p := by
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [rationalLogHeight, Real.log_le_iff_le_exp (lt_of_lt_of_le hd (le_max_right _ _)), max_le_iff]

theorem rationalLogHeight_nonneg (q : ℚ) : 0 ≤ rationalLogHeight q := by
  apply Real.log_nonneg
  have hd : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  exact hd.trans (le_max_right _ _)

theorem rationalHeightLE_ceil_exp {q : ℚ} {p : ℝ} (h : rationalLogHeight q ≤ p) :
    RationalHeightLE q ⌈Real.exp p⌉₊ := by
  obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff q p).mp h
  exact ⟨Nat.cast_le.mp (hn.trans (Nat.le_ceil _)), Nat.cast_le.mp (hd.trans (Nat.le_ceil _))⟩

theorem rationalLogHeight_le_of_height {q : ℚ} {H : ℕ} {p : ℝ}
    (hq : RationalHeightLE q H) (hH : (H : ℝ) ≤ Real.exp p) :
    rationalLogHeight q ≤ p :=
  (rationalLogHeight_le_iff q p).mpr
    ⟨(Nat.cast_le.mpr hq.1).trans hH, (Nat.cast_le.mpr hq.2).trans hH⟩

theorem one_le_ceil_exp (p : ℝ) : 1 ≤ ⌈Real.exp p⌉₊ :=
  Nat.one_le_ceil_iff.mpr (Real.exp_pos p)

theorem ceil_exp_le_exp_add_one {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := by
  have h1 : 1 ≤ Real.exp p := by simpa using Real.exp_le_exp.mpr hp
  calc
    _ ≤ Real.exp p + 1 := (Nat.ceil_lt_add_one (Real.exp_pos p).le).le
    _ ≤ 2 * Real.exp p := by linarith
    _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos p).le
    _ = Real.exp (p + 1) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

theorem exists_bounded_sorted_adapted_basis_logHeight {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hv : ∀ i j k, rationalLogHeight (e.repr (v i j : L) k) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ s + 1) ∧ IsCentralLieBasis b ∧
      (∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (e i) j) ≤ (p + 3) ^ 5) ∧
      ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := hp.trans (le_add_of_nonneg_right zero_le_one)
  have hd1 : (Fintype.card ι : ℝ) ≤ p + 1 := hd.trans (le_add_of_nonneg_right zero_le_one)
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis e] using hd1
  obtain ⟨b, w, hw, hbound, hcentral, hb, hlayer⟩ :=
    F.exists_bounded_sorted_adapted_basis e v hspan
      (fun i j k => rationalHeightLE_ceil_exp (hv i j k))
  have hinverse := inverse_basis_entries_height e b hH hb
  have hstructure := basis_change_structure_height e b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
  refine ⟨b, w, hw, hbound, hcentral, hlayer,
    fun j i => rationalLogHeight_le_of_height (hb j i) hHp, ?_, ?_⟩
  · intro i j
    apply rationalLogHeight_le_of_height (hinverse i j)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalSolveHeight_le_budget (Fintype.card (Fin (finrank ℚ L))) H hp1 hr hHp
  · intro i j k
    apply rationalLogHeight_le_of_height (hstructure i j k)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalLieStructureHeight_inverse_budget (Fintype.card ι)
        (Fintype.card (Fin (finrank ℚ L))) H hp1 hd1 hr hHp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

noncomputable def boundedRationalCandidates (H : ℕ) : Finset ℚ := by
  classical
  exact ((Finset.Icc (-(H : ℤ)) H) ×ˢ Finset.range (H + 1)).image
    (fun z : ℤ × ℕ => (z.1 : ℚ) / z.2)

theorem mem_boundedRationalCandidates {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) :
    q ∈ boundedRationalCandidates H := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(q.num, q.den), Finset.mem_product.mpr ⟨?_, ?_⟩, Rat.num_div_den q⟩
  · apply Finset.mem_Icc.mpr
    have hn : |q.num| ≤ (H : ℤ) := by
      simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hq.1)
    exact abs_le.mp hn
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hq.2)

theorem boundedRationalCandidates_card (H : ℕ) :
    (boundedRationalCandidates H).card ≤ (2 * H + 1) * (H + 1) := by
  classical
  have hcard : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
    rw [Int.card_Icc]
    omega
  exact Finset.card_image_le.trans (by rw [Finset.card_product, hcard, Finset.card_range])

theorem finite_card_bounded_height_arrays {ι : Type*} [Fintype ι]
    (S : Set (ι → ℚ)) (H : ℕ) (hS : ∀ x ∈ S, ∀ i, RationalHeightLE (x i) H) :
    S.Finite ∧ S.ncard ≤ ((2 * H + 1) * (H + 1)) ^ Fintype.card ι := by
  classical
  let f : S → (ι → ↥(boundedRationalCandidates H)) :=
    fun x i => ⟨x.val i, mem_boundedRationalCandidates (hS x x.property i)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  let : Finite S := Finite.of_injective f hf
  have hc := Nat.card_le_card_of_injective f hf
  have hb := Nat.pow_le_pow_left (boundedRationalCandidates_card H) (Fintype.card ι)
  refine ⟨Set.toFinite S, ?_⟩
  have hbound : S.ncard ≤ (boundedRationalCandidates H).card ^ Fintype.card ι := by
    simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Fintype.card_fun, Fintype.card_coe] using hc
  exact hbound.trans hb

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_normalized_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℚ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ r : VectorPolynomial σ ℚ D.filtration.realification.squareLieSubalgebra,
          D.filtration.realification.squareFiltration.Adapted w r ∧
          VectorPolynomial.map D.filtration.realification.squareFst.toLinearMap r =
            normalizedShiftLog s h (-ε.coord) (-γ.coord) f.log ∧
          VectorPolynomial.map D.filtration.realification.squareSnd.toLinearMap r = f.log := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  let H := ⌈Real.exp p⌉₊
  let u : D.RealGroup := ⟨eval h f.log⟩
  let v : D.RealGroup := ⟨eval (fun _ => 0) f.log⟩
  obtain ⟨ε, hε, γ, hγ, heq⟩ := hrep D.basis D.filtration.lowerCentralSeries_eq_bot
    D.lattice D.grid H (p + 1) D.grid_pos D.inner_grid
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) (u * v⁻¹)
  refine ⟨ε, γ, hγ, hε, ?_⟩
  exact D.filtration.realification.exists_normalized_shift_square w hw h (-ε.coord) (-γ.coord)
    f.log f.adapted (D.filtration.realification.normalizedShift_horizontal_zero h f.log ε γ heq)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem rational_functional_value_logHeight {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) (eta : V →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (heta : ∀ i, rationalLogHeight (eta (b i)) ≤ p)
    (x : V) (hx : ∀ i, rationalLogHeight (b.repr x i) ≤ p) :
    rationalLogHeight (eta x) ≤ (p + 2) ^ 4 := by
  classical
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hterms (i) : RationalHeightLE (b.repr x i * eta (b i)) (H * H) :=
    (rationalHeightLE_ceil_exp (hx i)).mul (rationalHeightLE_ceil_exp (heta i))
  have hHH : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp (p + 1) := by gcongr
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  have he : eta x = ∑ i, b.repr x i * eta (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [he]
  apply rationalLogHeight_le_of_height (rationalHeightLE_sum _ hterms)
  exact rational_sum_cost_le_exp (Fintype.card ι) (H * H) hp 2 1 hHH
    (by simpa only [pow_one] using hι.trans (show p ≤ p + 2 by linarith))

end Erdos3

end

section

namespace Erdos3

open Module

theorem linearMap_coordinate_logHeight
    {V W ι κ : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [Fintype ι]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (T : V →ₗ[ℚ] W)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hT : ∀ i j, rationalLogHeight (f.repr (T (e i)) j) ≤ p)
    (x : V) (hx : ∀ i, rationalLogHeight (e.repr x i) ≤ p) (j : κ) :
    rationalLogHeight (f.repr (T x) j) ≤ (p + 2) ^ 4 := by
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hHH : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp (p + 1) :=
        mul_le_mul hH hH (Nat.cast_nonneg H) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  have hraw := linearMap_coordinate_height e f T
    (fun i j => rationalHeightLE_ceil_exp (hT i j)) x
    (fun i => rationalHeightLE_ceil_exp (hx i)) j
  apply rationalLogHeight_le_of_height hraw
  exact rational_sum_cost_le_exp (Fintype.card ι) (H * H) hp 2 1 hHH
    (by simpa only [pow_one] using hn.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_layer_basis (a : σ → ℕ) (ha : a ≤ bound) {p : ℝ}
    (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.layer a))) ℚ (M.filtration.layer a),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  let a' : ∀ i, Fin (bound i + 1) := fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩
  exact ⟨M.basis a', hM.2 a'⟩

theorem exists_ordinary_layer_basis (n : Fin (s + 1)) {p : ℝ}
    (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.ordinary.layer (n.val + 1)))) ℚ
        (M.filtration.ordinary.layer (n.val + 1)),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  rw [M.ordinary]
  exact ⟨D.layerBasis n, hM.1.2.2.2 n⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_positive_layer_basis (n : ℕ) (hn : 1 ≤ n) {p : ℝ}
    (hD : D.GeometryComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.layer n))) ℚ (D.filtration.layer n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases hms : m < s + 1
  · exact ⟨D.layerBasis ⟨m, hms⟩, hD.2.2.2 ⟨m, hms⟩⟩
  · have hzero : D.filtration.layer (m + 1) = ⊥ := by
      apply bot_unique
      exact (D.filtration.antitone (by omega : s + 1 ≤ m + 1)).trans_eq D.filtration.terminal
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    let b := Module.finBasis ℚ (D.filtration.layer (m + 1))
    refine ⟨b, fun j k => ?_⟩
    have hb : (b j : L) = 0 := by
      have h := (b j).property
      simpa only [hzero, Submodule.mem_bot] using h
    rw [hb]
    simpa [rationalLogHeight] using (Nat.cast_nonneg d).trans hD.1

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_native_complex_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (E.realLattice ⊓ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).range ≤
        D.realLattice.map (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ)) →
      ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
      (letI := D.metricSpace; LipschitzWith ℓ u) → (∀ x, ‖u x‖ ≤ 1) →
      (∀ k ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
        u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
      ∃ (v : E.Space → ℂ) (K : ℝ≥0),
        (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := E.metricSpace; LipschitzWith K v) ∧
        (∀ y, ‖v y‖ ≤ 2) ∧
        ∀ x, v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨c, _, hrec⟩ := exists_controlled_rational_image_reconstruction s
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ hcover u ℓ hℓ hu hub hker
  have ht : 0 ≤ p + 1 := by linarith
  have hpt : p ≤ p + 1 := by linarith
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr hpt
  obtain ⟨v, K, hK, hv, hb, heval⟩ := hrec D.filtration.lowerCentralSeries_eq_bot
    E.filtration.lowerCentralSeries_eq_bot D.basis E.basis φ D.lattice E.lattice
    D.grid E.grid ⌈Real.exp p⌉₊ D.grid_pos E.grid_pos (one_le_ceil_exp p)
    D.outer_grid E.inner_grid E.outer_grid
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
    (fun i j => rationalHeightLE_ceil_exp (hφ i j)) hcover u hker ℓ 1 hu hub
    (p + 1) ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt)
    (ceil_exp_le_exp_add_one hp) (hE.2.1.trans hexp) (hℓ.trans hexp)
    (by simpa only [NNReal.coe_one] using Real.one_le_exp ht)
  have hcost : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv,
    fun y => by simpa only [NNReal.coe_one, mul_one] using hb y, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

theorem RationalHeightLE.pow {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) (n : ℕ) :
    RationalHeightLE (q ^ n) (H ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using rationalHeightLE_one (by decide : 1 ≤ 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hq

theorem ceil_exp_power_le_exp {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ((⌈Real.exp p⌉₊ ^ n : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * (p + 1)) := by
  rw [Nat.cast_pow, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (ceil_exp_le_exp_add_one hp) n

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.DetectedTranslationSeparationBudget
namespace OAI

section

namespace Erdos3

theorem detectedTranslationSeparation_budget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + 3) ^ 5 ∧
      (p + 3) ^ 3 ≤ (p + 3) ^ 5 ∧
      (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 5) := by
  have hbase : 1 ≤ p + 3 := by linarith
  have hlinear : p + 3 ≤ (p + 3) ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 5)
  refine ⟨(by linarith), pow_le_pow_right₀ hbase (by decide : 3 ≤ 5), ?_⟩
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4)).trans
  apply Real.exp_le_exp.mpr
  have hfour : (p + 2) ^ 4 ≤ (p + 3) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hone : 1 ≤ (p + 3) ^ 4 := one_le_pow₀ hbase
  calc
    (p + 2) ^ 4 + 1 ≤ 2 * (p + 3) ^ 4 := by linarith
    _ ≤ (p + 3) * (p + 3) ^ 4 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (p + 3) ^ 5 := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SquarefreeModelBudget
namespace OAI

section

namespace Erdos3

theorem squarefreeBracketHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (squarefreeBracketHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hcube : ((H * H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p := by
        push_cast
        gcongr
      _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hsq : ((n ^ 2 : ℕ) : ℝ) ≤ (p + 2) ^ 2 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (hn.trans (by linarith)) 2
  exact rational_sum_cost_le_exp (n ^ 2) (H * H * H) hp 2 2 hcube hsq

theorem squarefreeStructureHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (squarefreeStructureHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 8) := by
  have hprod : ((rationalSolveHeight n H * squarefreeBracketHeight n H : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 6) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 5) * Real.exp ((p + 2) ^ 5) :=
        mul_le_mul (rationalSolveHeight_le_budget n H hp hn hH)
          (squarefreeBracketHeight_le_exp n H hp hn hH) (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * (p + 2) ^ 5) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (p + 2) * (p + 2) ^ 5 := by gcongr; linarith
          _ = _ := by ring
  exact rational_sum_cost_le_exp n _ hp 6 1 hprod (by simpa only [pow_one] using hn.trans (by linarith))

end Erdos3

end

section

namespace Erdos3

noncomputable def squarefreeInputBudget (t : ℕ) (p : ℝ) : ℝ := (2 : ℝ) ^ t * p + (p + 3) ^ 8

theorem squarefreeInputBudget_nonneg (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ squarefreeInputBudget t p := by
  unfold squarefreeInputBudget
  positivity

theorem le_squarefreeInputBudget (t : ℕ) {p : ℝ} (hp : 0 ≤ p) : p ≤ squarefreeInputBudget t p := by
  have hp2 : p ≤ (2 : ℝ) ^ t * p := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hp
  exact hp2.trans (le_add_of_nonneg_right (by positivity))

theorem squarefreeStructureHeight_ceil_exp (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) :
    (squarefreeStructureHeight n ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 8) := by
  have h := squarefreeStructureHeight_le_exp n ⌈Real.exp p⌉₊
    (p := p + 1) (by linarith) (by linarith) (ceil_exp_le_exp_add_one hp)
  have heq : p + 1 + 2 = p + 3 := by ring
  simpa only [heq] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.StepOneSplittingBudget
namespace OAI

section

namespace Erdos3

theorem stepOne_linear_budget {p : ℝ} (hp : 0 ≤ p) :
    3 * p + 1 ≤ (p + 2) ^ 4 := by
  have hs : 3 * p + 1 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  exact hs.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 2 ≤ 4))

theorem stepOne_denominator_budget {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 4) :=
  (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr
    ((show p + 1 ≤ 3 * p + 1 by linarith).trans (stepOne_linear_budget hp)))

theorem stepOne_slow_budget {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp p⌉₊ : ℝ) / (2 * (Real.exp (-p) / Real.exp p)) ≤ Real.exp ((p + 2) ^ 4) := by
  have hδ : 0 < Real.exp (-p) / Real.exp p := div_pos (Real.exp_pos _) (Real.exp_pos _)
  calc
    _ ≤ (⌈Real.exp p⌉₊ : ℝ) / (Real.exp (-p) / Real.exp p) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (by linarith)
    _ ≤ Real.exp (p + 1) / (Real.exp (-p) / Real.exp p) :=
      div_le_div_of_nonneg_right (ceil_exp_le_exp_add_one hp) hδ.le
    _ = Real.exp (3 * p + 1) := by
      rw [← Real.exp_sub, ← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (stepOne_linear_budget hp)

theorem stepOne_kernel_height_budget {p : ℝ} (hp : 0 ≤ p) :
    ((2 * ⌈Real.exp p⌉₊ ^ 2 : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    _ ≤ Real.exp 1 * (Real.exp (p + 1)) ^ 2 := by
      apply mul_le_mul
      · have h := Real.add_one_le_exp (1 : ℝ)
        linarith only [h]
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (ceil_exp_le_exp_add_one hp) 2
      · positivity
      · positivity
    _ = Real.exp (2 * p + 3) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h : 2 * p + 3 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
      exact h.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 2 ≤ 4))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCentralSeed
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_central_character_extension (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ T : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (hT : ∀ z ∈ T, ∀ v : L, ⁅z.coord, v⁆ = 0)
    (η : L →ₗ[ℝ] ℝ) (A : ℝ≥0) (hη : ∀ x, |η x| ≤ A * ‖e.equivFun x‖)
    (hint : ∀ γ ∈ Γ, ∃ n : ℤ, η γ.coord = n) :
    letI := quotientMetricSpace e Γ hΓ
    ∃ f : NilpotentLieBCHGroup L s hnil ⧸ Γ → ℂ,
      LipschitzWith (2 * logCharacterMetricConstant s (Fintype.card ι) H A) f ∧
      (∀ z ∈ T, f (QuotientGroup.mk z) = logCharacter η z) ∧ ∀ x, ‖f x‖ ≤ 2 := by
  let := quotientMetricSpace e Γ hΓ
  obtain ⟨f, hf, heq, hbound⟩ := exists_complex_extension_along_map
    (fun z : T => (QuotientGroup.mk z.val : _ ⧸ Γ)) (fun z : T => logCharacter η z.val)
    (logCharacterMetricConstant s (Fintype.card ι) H A) 1
    (central_logCharacter_coset_dist_le e c hstructure hc Γ T hΓ hT η A hη hint)
    (fun z => (logCharacter_norm η z.val).le)
  exact ⟨f, hf, fun z hz => heq ⟨z, hz⟩, by simpa only [NNReal.coe_one, mul_one] using hbound⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def realifyFunctional (η : L →ₗ[ℚ] ℚ) : (ℝ ⊗[ℚ] L) →ₗ[ℝ] ℝ :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight
    ((Algebra.linearMap ℚ ℝ).comp η))

@[simp]
theorem realifyFunctional_tmul (η : L →ₗ[ℚ] ℚ) (r : ℝ) (v : L) :
    realifyFunctional η (r ⊗ₜ[ℚ] v) = r * (η v : ℝ) := by
  simp [realifyFunctional]

noncomputable def basisFrequency {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (n : S → ℤ) : L →ₗ[ℚ] ℚ :=
  ∑ j : S, ((n j : ℚ) / (N : ℚ)) • b.coord j

theorem basisFrequency_apply {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (n : S → ℤ) (v : L) :
    basisFrequency b S N n v = ∑ j : S, ((n j : ℚ) / (N : ℚ)) * b.repr v j := by
  simp [basisFrequency, Basis.coord_apply]

theorem basisFrequency_basis {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (n : S → ℤ) (j : S) :
    basisFrequency b S N n (b j) = (n j : ℚ) / (N : ℚ) := by
  classical
  rw [basisFrequency_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hval : (j : ι) ≠ i := fun h => hij (Subtype.ext h.symm)
    simp [Basis.repr_self, hval]
  · simp

theorem realify_basisFrequency_direction {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (hN : 0 < N) (n : S → ℤ) (j : S) :
    realifyFunctional (basisFrequency b S N n) ((N : ℝ) • b.baseChange ℝ j) = n j := by
  simp only [map_smul, Basis.baseChange_apply, realifyFunctional_tmul,
    basisFrequency_basis, one_mul, smul_eq_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  exact mul_div_cancel₀ _ (by exact_mod_cast hN.ne')

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_central_seed (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ f : D.Space → ℂ, (letI := D.metricSpace; LipschitzWith K f) ∧
        (∀ x, ‖f x‖ ≤ 2) ∧ ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
          f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z := by
  obtain ⟨a, _, hcost⟩ := exists_logCharacterMetricConstant_exp_bound s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget ((2 * X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  let := D.metricSpace
  let H := ⌈Real.exp p⌉₊
  let A : ℝ≥0 := d * H
  have hlinear (x : ℝ ⊗[ℚ] L) : |realifyFunctional η x| ≤
      A * ‖(D.basis.baseChange ℝ).equivFun x‖ := by
    have h := abs_linearMap_le_basis_bound (D.basis.baseChange ℝ) (realifyFunctional η)
      (H : ℝ≥0) (fun i => by
        simpa only [Basis.baseChange_apply, realifyFunctional_tmul, one_mul, NNReal.coe_natCast] using
          (rationalHeightLE_ceil_exp (hη i)).abs_real_le) x
    simpa only [Fintype.card_fin, A, NNReal.coe_mul, NNReal.coe_natCast] using h
  obtain ⟨f, hf, hseed, hnorm⟩ := exists_central_character_extension (D.basis.baseChange ℝ)
    (lieStructureConstants D.basis) (fun i j k => (realLieBasis_structure D.basis i j k).symm)
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    D.realLattice (D.filtration.realification.subgroup s) D.realLattice_closed_discrete.1
    (fun z hz v => D.filtration.realification.top_layer_central hz v)
    (realifyFunctional η) A hlinear hint
  let K := 2 * logCharacterMetricConstant s d H A
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hA : (A : ℝ) ≤ Real.exp (2 * p + 1) := by
    have hd : (d : ℝ) ≤ Real.exp p := hD.1.trans (by linarith [Real.add_one_le_exp p])
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) := mul_le_mul hd hH (Nat.cast_nonneg H) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hK : (K : ℝ) ≤ Real.exp ((2 * p + 1 + a) ^ a) :=
    hcost d H A (2 * p + 1) (by positivity) (hD.1.trans (by linarith))
      (hH.trans (Real.exp_le_exp.mpr (by linarith))) hA
  have hpc : (2 * p + 1 + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hpoly p hp
  refine ⟨K, hK.trans (Real.exp_le_exp.mpr hpc), f, ?_, hnorm, hseed⟩
  simp only [Fintype.card_fin] at hf
  convert hf using 1
  rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRationalRepresentatives
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_rational_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup, (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          (∃ r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ) ∧
          (∃ r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = γ * r) := by
  obtain ⟨a, _, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hclosure⟩ := exists_real_bch_rational_closure s
  let X : Polynomial ℕ := Polynomial.X
  let P := (2 * X + 1 + Polynomial.C a) ^ a + (2 * X + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD q hq hqp
  let t := 2 * p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := (ceil_exp_le_exp_add_one hp).trans
    (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by
    simpa only [Fintype.card_fin] using hD.1.trans hpt
  have hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hprod : ((q * D.grid : ℕ) : ℝ) ≤ Real.exp t := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hqp hD.2.1 (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨m, hm, hmb, _, hmul, _⟩ := hclosure D.basis H t
    D.filtration.lowerCentralSeries_eq_bot ht hd hH hc (q * D.grid)
    (Nat.mul_pos hq D.grid_pos) hprod
  have hsum : (t + a) ^ a + (t + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (t + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (t + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg ht (Nat.cast_nonneg a)) _)).trans hsum
  have hright (g : D.RealGroup) (hg : (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q) :
      ∃ r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
        ∃ γ ∈ D.realLattice, g = r * γ := by
    obtain ⟨r, hr, γ, hγ, heq⟩ := hrep D.basis D.filtration.lowerCentralSeries_eq_bot
      D.lattice D.grid H t D.grid_pos D.inner_grid hc ht hd hH
      (hD.2.1.trans (Real.exp_le_exp.mpr hpt)) g
    have hγgrid := realification_subgroup_grid D.basis D.lattice D.grid D.outer_grid
      γ⁻¹ (D.realLattice.inv_mem hγ)
    have hrgrid : (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m := by
      have h := hmul g γ⁻¹
        (realDenominatorGrid_subset_of_dvd hq (dvd_mul_right q D.grid) hg)
        (realDenominatorGrid_subset_of_dvd D.grid_pos (dvd_mul_left D.grid q) hγgrid)
      simpa only [heq, mul_inv_cancel_right] using h
    exact ⟨r, fun i => (hr i).trans (Real.exp_le_exp.mpr haC), hrgrid, γ, hγ, heq⟩
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hg
  refine ⟨hright g hg, ?_⟩
  have hginv : (D.basis.baseChange ℝ).equivFun g⁻¹.coord ∈ realDenominatorGrid q := by
    change (D.basis.baseChange ℝ).equivFun (-g.coord) ∈ _
    rw [map_neg]
    exact realDenominatorGrid_neg q hg
  obtain ⟨r, hr, hrgrid, γ, hγ, heq⟩ := hright g⁻¹ hginv
  refine ⟨r⁻¹, ?_, ?_, γ⁻¹, D.realLattice.inv_mem hγ, ?_⟩
  · intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hr i
  · change (D.basis.baseChange ℝ).equivFun (-r.coord) ∈ _
    rw [map_neg]
    exact realDenominatorGrid_neg m hrgrid
  · have h := congrArg (fun z : D.RealGroup => z⁻¹) heq
    simpa only [inv_inv, mul_inv_rev] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialSubstitutionPoint
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (x : σ → R) : σ → R :=
  fun i => aeval x (F (X i))

theorem polynomialSubstitutionPoint_aeval
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (x : σ → R) (P : MvPolynomial σ R) :
    aeval (polynomialSubstitutionPoint F x) P = aeval x (F P) := by
  conv_rhs => rw [MvPolynomial.aeval_unique F, MvPolynomial.comp_aeval_apply]
  rfl

noncomputable def polynomialPointEquiv
    (e : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) : Equiv.Perm (σ → R) where
  toFun := polynomialSubstitutionPoint e.symm.toAlgHom
  invFun := polynomialSubstitutionPoint e.toAlgHom
  left_inv x := by
    funext i
    change aeval (polynomialSubstitutionPoint e.symm.toAlgHom x) (e (X i)) = x i
    rw [polynomialSubstitutionPoint_aeval]
    change aeval x (e.symm (e (X i))) = x i
    rw [e.symm_apply_apply, aeval_X]
  right_inv x := by
    funext i
    change aeval (polynomialSubstitutionPoint e.toAlgHom x) (e.symm (X i)) = x i
    rw [polynomialSubstitutionPoint_aeval]
    change aeval x (e (e.symm (X i))) = x i
    rw [e.apply_symm_apply, aeval_X]

noncomputable def polynomialPointAction :
    (MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) →* Equiv.Perm (σ → R) where
  toFun := polynomialPointEquiv
  map_one' := by
    ext x i
    change aeval x (X i) = x i
    exact aeval_X x i
  map_mul' e f := by
    ext x i
    change aeval x (f.symm (e.symm (X i))) =
      aeval (polynomialSubstitutionPoint f.symm.toAlgHom x) (e.symm (X i))
    exact (polynomialSubstitutionPoint_aeval f.symm.toAlgHom x (e.symm (X i))).symm

noncomputable def weightedLoweringPointAction (w : σ → ℕ) :
    WeightedLoweringAut w R →* Equiv.Perm (σ → R) :=
  polynomialPointAction.comp (weightedLoweringSubgroup w).subtype

theorem polynomial_map_aeval {S : Type*} [CommRing S] (f : R →+* S)
    (x : σ → R) (P : MvPolynomial σ R) :
    aeval (fun i => f (x i)) (MvPolynomial.map f P) = f (aeval x P) := by
  simpa only [MvPolynomial.aeval_eq_eval, Function.comp_def] using
    (MvPolynomial.map_eval f x P).symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem integerCoefficientPolynomials_aeval {P : MvPolynomial σ ℚ}
    (hP : P ∈ integerCoefficientPolynomials σ) (b : σ → ℤ) :
    ∃ z : ℤ, aeval (fun i => (b i : ℚ)) P = (z : ℚ) := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  exact ⟨aeval b Q, polynomial_map_aeval (Int.castRingHom ℚ) b Q⟩

theorem integerTupleRatCast_injective :
    Function.Injective (fun b : σ → ℤ => fun i => (b i : ℚ)) := by
  intro b c h
  funext i
  have hi : (b i : ℚ) = (c i : ℚ) := congrFun h i
  exact_mod_cast hi

noncomputable def integerWeightedLoweringPoint (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) : σ → ℤ :=
  fun i => Classical.choose (integerCoefficientPolynomials_aeval
    ((integerWeightedLoweringSubgroup w).inv_mem he i) b)

theorem integerWeightedLoweringPoint_cast (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) :
    (fun i => (integerWeightedLoweringPoint e he b i : ℚ)) =
      weightedLoweringPointAction w e (fun i => (b i : ℚ)) := by
  funext i
  exact (Classical.choose_spec (integerCoefficientPolynomials_aeval
    ((integerWeightedLoweringSubgroup w).inv_mem he i) b)).symm

theorem integerWeightedLoweringPoint_inv (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) :
    integerWeightedLoweringPoint e⁻¹ ((integerWeightedLoweringSubgroup w).inv_mem he)
      (integerWeightedLoweringPoint e he b) = b := by
  apply integerTupleRatCast_injective
  change (fun i => (integerWeightedLoweringPoint e⁻¹ _ (integerWeightedLoweringPoint e he b) i : ℚ)) =
    (fun i => (b i : ℚ))
  rw [integerWeightedLoweringPoint_cast, integerWeightedLoweringPoint_cast, map_inv]
  exact (weightedLoweringPointAction w e).symm_apply_apply _

noncomputable def integerWeightedLoweringPointEquiv (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) : Equiv.Perm (σ → ℤ) where
  toFun := integerWeightedLoweringPoint e he
  invFun := integerWeightedLoweringPoint e⁻¹ ((integerWeightedLoweringSubgroup w).inv_mem he)
  left_inv := integerWeightedLoweringPoint_inv e he
  right_inv b := by
    apply integerTupleRatCast_injective
    change (fun i => (integerWeightedLoweringPoint e he (integerWeightedLoweringPoint e⁻¹ _ b) i : ℚ)) =
      (fun i => (b i : ℚ))
    rw [integerWeightedLoweringPoint_cast, integerWeightedLoweringPoint_cast, map_inv]
    exact (weightedLoweringPointAction w e).apply_symm_apply _

theorem integerWeightedLoweringPointEquiv_cast (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) :
    (fun i => (integerWeightedLoweringPointEquiv e he b i : ℚ)) =
      weightedLoweringPointAction w e (fun i => (b i : ℚ)) :=
  integerWeightedLoweringPoint_cast e he b

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

theorem polynomialShear_integral_iff (D : PolynomialShearLieAlgebra w ℚ) :
    (∀ i, D.val (X i) ∈ integerCoefficientPolynomials σ) ↔
      ∀ a : PolynomialShearIndex w, ∃ z : ℤ, (polynomialShearBasis (R := ℚ) w).repr D a = (z : ℚ) := by
  constructor
  · intro h a
    exact (mem_integerCoefficientPolynomials_iff _).mp (h a.1) a.2.val
  · intro h i
    apply (mem_integerCoefficientPolynomials_iff _).mpr
    intro a
    by_cases ha : Finsupp.weight w a + 1 ≤ w i
    · exact h ⟨i, a, ha⟩
    · refine ⟨0, ?_⟩
      apply not_ne_iff.mp
      intro hc
      apply ha
      exact D.property i (MvPolynomial.mem_support_iff.mpr hc)

variable [Fintype (PolynomialShearIndex w)]

theorem polynomialShear_integralVector_iff (D : PolynomialShearLieAlgebra w ℚ) :
    (∀ i, D.val (X i) ∈ integerCoefficientPolynomials σ) ↔
      IntegralVector ((polynomialShearBasis (R := ℚ) w).equivFun D) := by
  rw [polynomialShear_integral_iff]
  constructor
  · intro h
    choose z hz using h
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩ a
    exact ⟨z a, hz a⟩

theorem polynomialShear_denominatorGrid_iff (B : ℕ) (D : PolynomialShearLieAlgebra w ℚ) :
    (polynomialShearBasis (R := ℚ) w).equivFun D ∈ denominatorGrid B ↔
      ∀ i, ((B : ℚ) • D).val (X i) ∈ integerCoefficientPolynomials σ := by
  change IntegralVector ((B : ℚ) • (polynomialShearBasis (R := ℚ) w).equivFun D) ↔ _
  rw [← map_smul]
  exact (polynomialShear_integralVector_iff _).symm

theorem polynomialShear_scaledGrid_normalize (B : ℕ) (hB : 0 < B)
    (D : PolynomialShearLieAlgebra w ℚ)
    (hD : (polynomialShearBasis (R := ℚ) w).equivFun D ∈ scaledIntegerGrid B) :
    ∀ i, ((B : ℚ)⁻¹ • D).val (X i) ∈ integerCoefficientPolynomials σ := by
  obtain ⟨z, hz⟩ := hD
  apply (polynomialShear_integralVector_iff _).mpr
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hv : (polynomialShearBasis (R := ℚ) w).equivFun ((B : ℚ)⁻¹ • D) = fun i => (z i : ℚ) := by
    rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hBq, one_smul]
  exact ⟨z, congrFun hv⟩

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ : Type*} {w : σ → ℕ}

theorem polynomialShearMonomial_pderiv (a : PolynomialShearIndex w) :
    (polynomialShearMonomial (R := ℚ) w a).val =
      monomial a.2.val (1 : ℚ) • pderiv a.1 := by
  classical
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMonomial_X]
  change (if i = a.1 then monomial a.2.val (1 : ℚ) else 0) =
    monomial a.2.val (1 : ℚ) * pderiv a.1 (X i)
  by_cases h : i = a.1
  · subst i
    simp
  · simp [h]

theorem polynomialShearMonomial_monomial (a : PolynomialShearIndex w)
    (b : σ →₀ ℕ) (c : ℚ) :
    (polynomialShearMonomial (R := ℚ) w a).val (monomial b c) =
      monomial (a.2.val + (b - Finsupp.single a.1 1)) (c * b a.1) := by
  rw [polynomialShearMonomial_pderiv]
  change monomial a.2.val (1 : ℚ) * pderiv a.1 (monomial b c) = _
  rw [pderiv_monomial, MvPolynomial.monomial_mul, one_mul]

theorem polynomialShearMonomial_bracket_X [DecidableEq σ] (a b : PolynomialShearIndex w) (i : σ) :
    (⁅polynomialShearMonomial (R := ℚ) w a, polynomialShearMonomial w b⁆).val (X i) =
      (if i = b.1 then monomial (a.2.val + (b.2.val - Finsupp.single a.1 1)) (b.2.val a.1 : ℚ) else 0) -
      (if i = a.1 then monomial (b.2.val + (a.2.val - Finsupp.single b.1 1)) (a.2.val b.1 : ℚ) else 0) := by
  classical
  change ⁅(polynomialShearMonomial (R := ℚ) w a).val,
    (polynomialShearMonomial (R := ℚ) w b).val⁆ (X i) = _
  rw [Derivation.commutator_apply, polynomialShearMonomial_X, polynomialShearMonomial_X]
  split_ifs <;> simp only [map_zero, polynomialShearMonomial_monomial, one_mul]

noncomputable def polynomialShearBracketCoefficient (a b c : PolynomialShearIndex w) : ℤ := by
  classical
  exact (if c.1 = b.1 then
      if a.2.val + (b.2.val - Finsupp.single a.1 1) = c.2.val then (b.2.val a.1 : ℤ) else 0 else 0) -
    (if c.1 = a.1 then
      if b.2.val + (a.2.val - Finsupp.single b.1 1) = c.2.val then (a.2.val b.1 : ℤ) else 0 else 0)

variable [Fintype σ]

theorem polynomialShear_structureConstants (a b c : PolynomialShearIndex w) :
    lieStructureConstants (polynomialShearBasis w) a b c =
      (polynomialShearBracketCoefficient a b c : ℚ) := by
  classical
  rw [lieStructureConstants, polynomialShearBasis_repr,
    polynomialShearBasis_eq_monomial, polynomialShearBasis_eq_monomial,
    polynomialShearMonomial_bracket_X, coeff_sub]
  simp only [polynomialShearBracketCoefficient, Int.cast_sub, Int.cast_ite,
    Int.cast_natCast, Int.cast_zero]
  split_ifs <;> simp_all [coeff_monomial]

omit [Fintype σ] in
theorem polynomialShearBracketCoefficient_natAbs_le (s : ℕ)
    (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) (a b c : PolynomialShearIndex w) :
    (polynomialShearBracketCoefficient a b c).natAbs ≤ 2 * s := by
  classical
  have ha : a.2.val b.1 ≤ s := (Finsupp.le_weight w (hpos b.1).ne' a.2.val).trans
    ((Nat.le_add_right _ 1).trans (a.2.property.trans (hw a.1)))
  have hb : b.2.val a.1 ≤ s := (Finsupp.le_weight w (hpos a.1).ne' b.2.val).trans
    ((Nat.le_add_right _ 1).trans (b.2.property.trans (hw b.1)))
  unfold polynomialShearBracketCoefficient
  have hleft : (if c.1 = b.1 then
      if a.2.val + (b.2.val - Finsupp.single a.1 1) = c.2.val then (b.2.val a.1 : ℤ) else 0 else 0).natAbs ≤ s := by
    split_ifs <;> simp_all
  have hright : (if c.1 = a.1 then
      if b.2.val + (a.2.val - Finsupp.single b.1 1) = c.2.val then (a.2.val b.1 : ℤ) else 0 else 0).natAbs ≤ s := by
    split_ifs <;> simp_all
  exact (Int.natAbs_sub_le _ _).trans ((Nat.add_le_add hleft hright).trans_eq (by omega))

theorem polynomialShear_structureConstants_height (s : ℕ)
    (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) (a b c : PolynomialShearIndex w) :
    RationalHeightLE (lieStructureConstants (polynomialShearBasis w) a b c) (2 * s + 1) := by
  rw [polynomialShear_structureConstants]
  constructor
  · simpa using (polynomialShearBracketCoefficient_natAbs_le s hpos hw a b c).trans
      (Nat.le_succ (2 * s))
  · simp

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*}

noncomputable def polynomialShearLattice (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Subgroup (polynomialShearFiltration w s hw).Group :=
  (integerWeightedLoweringSubgroup w).comap (polynomialShearBCHEquiv w s hw).toMonoidHom

variable [Fintype σ] {w : σ → ℕ} [Fintype (PolynomialShearIndex w)]

theorem polynomialShearLattice_inner_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    scaledIntegerGrid s.factorial ⊆
      bchSubgroupCoordinates (polynomialShearBasis w) (polynomialShearLattice w s hw) := by
  intro x hx
  let D := (polynomialShearBasis (R := ℚ) w).equivFun.symm x
  have hD : (polynomialShearBasis (R := ℚ) w).equivFun D ∈ scaledIntegerGrid s.factorial := by
    simpa only [D, LinearEquiv.apply_symm_apply] using hx
  have hI := polynomialShear_scaledGrid_normalize s.factorial (Nat.factorial_pos s) D hD
  have he := polynomialShear_factorial_exp_integral s hw ((s.factorial : ℚ)⁻¹ • D) hI
  have hc : (s.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero s)
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul] at he
  exact he

theorem polynomialShearLattice_outer_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    bchSubgroupCoordinates (polynomialShearBasis w) (polynomialShearLattice w s hw) ⊆
      denominatorGrid s.factorial := by
  intro x hx
  let D := (polynomialShearBasis (R := ℚ) w).equivFun.symm x
  have hE : polynomialShearExpAut D ∈ integerWeightedLoweringSubgroup w := hx
  have hI (i : σ) := polynomialShear_factorial_log_integral s hw (polynomialShearExpAut D) hE i
  simp only [polynomialShearLog_exp] at hI
  have h := (polynomialShear_denominatorGrid_iff s.factorial D).mpr hI
  simpa only [D, LinearEquiv.apply_symm_apply] using h

noncomputable def polynomialShearRealLattice (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Subgroup (polynomialShearFiltration w s hw).realification.Group :=
  (polynomialShearLattice w s hw).map NilpotentLieBCHGroup.realificationHom

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]

theorem polynomialShearRealLattice_closed_discrete (s : ℕ) (hw : ∀ i, w i ≤ s) :
    IsClosed (polynomialShearRealLattice s hw : Set (polynomialShearFiltration w s hw).realification.Group) ∧
      IsDiscrete (polynomialShearRealLattice s hw : Set (polynomialShearFiltration w s hw).realification.Group) :=
  NilpotentLieBCHGroup.realification_subgroup_closed_discrete (polynomialShearBasis w)
    (polynomialShearLattice w s hw) s.factorial (Nat.factorial_pos s)
    (polynomialShearLattice_outer_grid s hw)

end Erdos3

end

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearIndexOrder :
    PolynomialShearIndex w ≃ Fin (Fintype.card (PolynomialShearIndex w)) :=
  let ρ := Fintype.equivFin (PolynomialShearIndex w)
  let u := fun j => polynomialShearDeficit w (ρ.symm j)
  ρ.trans (Tuple.sort u).symm

noncomputable def polynomialShearOrderedBasis :
    Basis (Fin (Fintype.card (PolynomialShearIndex w))) ℚ (PolynomialShearLieAlgebra w ℚ) :=
  (polynomialShearBasis w).reindex (polynomialShearIndexOrder w)

noncomputable def polynomialShearOrderedWeight (j : Fin (Fintype.card (PolynomialShearIndex w))) : ℕ :=
  polynomialShearDeficit w ((polynomialShearIndexOrder w).symm j)

theorem polynomialShearOrderedBasis_layers (r : ℕ) :
    polynomialShearLayer (R := ℚ) w r = Submodule.span ℚ
      (polynomialShearOrderedBasis w '' {j | r ≤ polynomialShearOrderedWeight w j}) := by
  change polynomialShearLayer w r = Submodule.span ℚ
    (((polynomialShearBasis (R := ℚ) w).reindex (polynomialShearIndexOrder w)) ''
      {j | r ≤ polynomialShearDeficit w ((polynomialShearIndexOrder w).symm j)})
  rw [basis_reindex_span_weights, polynomialShearLayer_span]

theorem polynomialShearOrderedBasis_structure_height (s : ℕ)
    (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) (a b c) :
    RationalHeightLE (lieStructureConstants (polynomialShearOrderedBasis w) a b c) (2 * s + 1) := by
  rw [polynomialShearOrderedBasis, lieStructureConstants_reindex]
  exact polynomialShear_structureConstants_height s hpos hw _ _ _

theorem polynomialShearOrderedBasis_inner_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    scaledIntegerGrid s.factorial ⊆
      bchSubgroupCoordinates (polynomialShearOrderedBasis w) (polynomialShearLattice w s hw) :=
  bchSubgroup_inner_grid_reindex (polynomialShearBasis w) (polynomialShearIndexOrder w) _
    (polynomialShearLattice_inner_grid s hw)

theorem polynomialShearOrderedBasis_outer_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    bchSubgroupCoordinates (polynomialShearOrderedBasis w) (polynomialShearLattice w s hw) ⊆
      denominatorGrid s.factorial :=
  bchSubgroup_outer_grid_reindex (polynomialShearBasis w) (polynomialShearIndexOrder w) _
    (polynomialShearLattice_outer_grid s hw)

theorem polynomialShearIndex_card_le (s : ℕ) (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) :
    Fintype.card (PolynomialShearIndex w) ≤ Fintype.card σ * (Fintype.card σ + 1) ^ s := by
  rw [← finrank_eq_card_basis (polynomialShearBasis (R := ℚ) w)]
  exact polynomialShear_finrank_le w hpos s hw

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)

noncomputable def polynomialShearRealPointAction :
    (polynomialShearFiltration w s hw).realification.Group →* Equiv.Perm (σ → ℝ) :=
  (weightedLoweringPointAction w).comp (polynomialShearRealAutEquiv w s hw).toMonoidHom

theorem polynomialShearRealPointAction_rational
    (g : (polynomialShearFiltration w s hw).Group) (x : σ → ℚ) :
    polynomialShearRealPointAction w s hw (NilpotentLieBCHGroup.realificationHom g)
        (fun i => (x i : ℝ)) =
      fun i => (weightedLoweringPointAction w (polynomialShearBCHEquiv w s hw g) x i : ℝ) := by
  funext i
  have h :
      (polynomialShearRealAutEquiv w s hw (NilpotentLieBCHGroup.realificationHom g)).val.symm (X i) =
      MvPolynomial.map (algebraMap ℚ ℝ) ((polynomialShearBCHEquiv w s hw g).val.symm (X i)) := by
    simpa only [map_inv, MvPolynomial.map_X, Subgroup.coe_inv, AlgEquiv.aut_inv] using
      polynomialShearRealAutEquiv_rational w s hw g⁻¹ (X i)
  change aeval (fun j => (x j : ℝ))
      ((polynomialShearRealAutEquiv w s hw (NilpotentLieBCHGroup.realificationHom g)).val.symm (X i)) =
    (aeval x ((polynomialShearBCHEquiv w s hw g).val.symm (X i)) : ℝ)
  rw [h]
  exact polynomial_map_aeval (algebraMap ℚ ℝ) x _

theorem polynomialShearRealLattice_integer_permutation
    (γ : (polynomialShearFiltration w s hw).realification.Group)
    (hγ : γ ∈ polynomialShearRealLattice s hw) :
    ∃ e : Equiv.Perm (σ → ℤ), ∀ b,
      polynomialShearRealPointAction w s hw γ (fun i => (b i : ℝ)) =
        fun i => (e b i : ℝ) := by
  obtain ⟨g, hg, rfl⟩ := hγ
  let e := integerWeightedLoweringPointEquiv (polynomialShearBCHEquiv w s hw g) hg
  refine ⟨e, fun b => ?_⟩
  have h := congrArg (fun x : σ → ℚ => fun i => (x i : ℝ))
    (integerWeightedLoweringPointEquiv_cast (polynomialShearBCHEquiv w s hw g) hg b)
  have hr := polynomialShearRealPointAction_rational w s hw g (fun i => (b i : ℚ))
  simpa only [Rat.cast_intCast] using hr.trans h.symm

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)

noncomputable def polynomialShearOrbitSum (K : (σ → ℝ) → ℝ)
    (g : (polynomialShearFiltration w s hw).realification.Group) : ℝ :=
  ∑' b : σ → ℤ, K (polynomialShearRealPointAction w s hw g (fun i => (b i : ℝ)))

theorem polynomialShearOrbitSum_lattice (K : (σ → ℝ) → ℝ)
    (g γ : (polynomialShearFiltration w s hw).realification.Group)
    (hγ : γ ∈ polynomialShearRealLattice s hw) :
    polynomialShearOrbitSum w s hw K (g * γ) = polynomialShearOrbitSum w s hw K g := by
  obtain ⟨e, he⟩ := polynomialShearRealLattice_integer_permutation w s hw γ hγ
  unfold polynomialShearOrbitSum
  simp_rw [map_mul, Equiv.Perm.mul_apply, he]
  exact e.tsum_eq (fun b : σ → ℤ => K (polynomialShearRealPointAction w s hw g (fun i => (b i : ℝ))))

noncomputable def polynomialShearQuotientSum (K : (σ → ℝ) → ℝ) :
    ((polynomialShearFiltration w s hw).realification.Group ⧸ polynomialShearRealLattice s hw) → ℝ :=
  Quotient.lift (polynomialShearOrbitSum w s hw K) (fun g h hgh => by
    have hi := polynomialShearOrbitSum_lattice w s hw K g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shearGroupLift (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) :
    (polynomialShearFiltration w s hw).realification.Group :=
  (polynomialShearRealAutEquiv w s hw).symm (A.loweringAt t)⁻¹

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def shearKernel (A : PolynomialPatch σ s d) (x : Fin d → ℝ) : ℝ :=
  A.kernel.value (fun i => aeval x (A.form.topResidualEquiv (X i)))

noncomputable def shearObservable (A : PolynomialPatch σ s d) :
    ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) → ℝ :=
  polynomialShearQuotientSum A.weight s A.weight_le A.shearKernel

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {τ : Type*} [Fintype τ] (w : τ → ℕ)

theorem polynomialShearRealificationEquiv_repr (D : ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) :
    (polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w D) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr D := by
  have he : polynomialShearRealificationEquiv w D = polynomialShearRealificationLinearEquiv w D :=
    DFunLike.congr_fun (polynomialShearRealificationMap_eq w) D
  rw [he]
  change (polynomialShearBasis (R := ℝ) w).repr
    ((polynomialShearBasis (R := ℝ) w).repr.symm
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr D)) = _
  exact LinearEquiv.apply_symm_apply _ _

theorem polynomialShearRealAutEquiv_symm_coord (s : ℕ) (hw : ∀ i, w i ≤ s)
    (e : WeightedLoweringAut w ℝ) :
    polynomialShearRealificationEquiv w ((polynomialShearRealAutEquiv w s hw).symm e).coord =
      polynomialShearLog e := by
  change polynomialShearRealificationEquiv w ((polynomialShearRealificationEquiv w).symm
    (polynomialShearLog e)) = _
  exact LieEquiv.apply_symm_apply _ _

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {v : Fin d → ℕ}

theorem shearGroupLift_coordinate (A : PolynomialSlots σ d v)
    (s : ℕ) (hv : ∀ i, v i ≤ s) (t : σ → ℝ) (a : PolynomialShearIndex v) :
    ((polynomialShearBasis (R := ℚ) v).baseChange ℝ).repr (A.shearGroupLift s hv t).coord a =
      -(polynomialShearBasis (R := ℝ) v).repr (polynomialShearLog (A.loweringAt t)) a := by
  change ((polynomialShearBasis (R := ℚ) v).baseChange ℝ).repr
    (((polynomialShearRealAutEquiv v s hv).symm (A.loweringAt t)⁻¹).coord) a = _
  rw [map_inv, NilpotentLieBCHGroup.coord_inv, map_neg, Finsupp.neg_apply]
  rw [← polynomialShearRealificationEquiv_repr, polynomialShearRealAutEquiv_symm_coord]

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shearCoordinatePolynomial (A : PolynomialSlots σ d w)
    (a : PolynomialShearIndex w) : MvPolynomial σ ℝ :=
  -polynomialSlotCoefficient a.2.val (A.symbolicLogSlot a.1)

theorem shearCoordinatePolynomial_degree (A : PolynomialSlots σ d w) (a : PolynomialShearIndex w) :
    A.shearCoordinatePolynomial a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a) := by
  exact (weightedSupportLE _ _).neg_mem
    (polynomialSlotCoefficient_degree (fun _ : σ => 1) w (A.symbolicLogSlot_degree a.1) a.2.val)

theorem shearCoordinatePolynomial_eval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) (a : PolynomialShearIndex w) :
    aeval t (A.shearCoordinatePolynomial a) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr (A.shearGroupLift s hw t).coord a := by
  rw [shearGroupLift_coordinate, polynomialShearBasis_repr]
  unfold shearCoordinatePolynomial
  rw [map_neg, polynomialSlotCoefficient_eval]
  change -(patchParameterSpecialization t (A.symbolicLogSlot a.1)).coeff a.2.val = _
  rw [symbolicLogSlot_specialization]

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial Module VectorPolynomial
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ} [Fintype (PolynomialShearIndex w)]

noncomputable def shearLogPolynomial (A : PolynomialSlots σ d w) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) :=
  VectorPolynomial.ofCoordinates ((polynomialShearBasis (R := ℚ) w).baseChange ℝ)
    A.shearCoordinatePolynomial

theorem shearLogPolynomial_coordinate (A : PolynomialSlots σ d w) (a : PolynomialShearIndex w) :
    VectorPolynomial.coordinate
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom A.shearLogPolynomial =
      A.shearCoordinatePolynomial a :=
  VectorPolynomial.coordinate_ofCoordinates _ _ _

theorem shearLogPolynomial_adapted (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.Adapted (fun _ : σ => 1) A.shearLogPolynomial := by
  rw [NilpotentLieFiltration.adapted_iff_coefficients]
  intro α
  apply ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
    (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
    (fun j => polynomialShearLayer_span w j) _ _).mpr
  intro a ha
  change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
    (VectorPolynomial.coefficients A.shearLogPolynomial α) = 0
  have hc := congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α)
    (A.shearLogPolynomial_coordinate a)
  rw [VectorPolynomial.coeff_coordinate] at hc
  apply hc.trans
  by_contra h
  have hb : Finsupp.weight (fun _ : σ => 1) α ≤ polynomialShearDeficit w a :=
    A.shearCoordinatePolynomial_degree a (MvPolynomial.mem_support_iff.mpr h)
  exact ha hb

theorem shearLogPolynomial_eval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) :
    VectorPolynomial.eval₂ t A.shearLogPolynomial = (A.shearGroupLift s hw t).coord := by
  apply ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr.injective
  ext a
  change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
    (VectorPolynomial.eval₂ t A.shearLogPolynomial) = _
  rw [VectorPolynomial.coordinate_eval₂, shearLogPolynomial_coordinate]
  exact A.shearCoordinatePolynomial_eval s hw t a

noncomputable def shearPolynomialOrbit (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1) :=
  NilpotentLieFiltration.polynomialOrbitOfLog A.shearLogPolynomial (A.shearLogPolynomial_adapted s hw)

theorem shearPolynomialOrbit_realEval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) :
    (polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
      (fun _ : σ => 1) t (A.shearPolynomialOrbit s hw) = A.shearGroupLift s hw t := by
  apply NilpotentLieBCHGroup.ext
  exact A.shearLogPolynomial_eval s hw t

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def shearOrbit (A : PolynomialPatch σ s d) :
    (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : σ => 1) := by
  letI := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.form.shearPolynomialOrbit s A.weight_le

end Erdos3.PolynomialPatch

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLoweringTriangular
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem aeval_eq_of_weightedSupportLT {w : σ → ℕ} {n : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLT w n) (x y : σ → R)
    (hxy : ∀ i, w i < n → x i = y i) : aeval x P = aeval y P := by
  classical
  rw [← P.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial]
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun z => z ^ α i)
    (hxy i ((Finsupp.le_weight_of_ne_zero' w (Finsupp.mem_support_iff.mp hi)).trans_lt (hP hα)))

variable {d : ℕ} {w : Fin d → ℕ}

theorem weightedLoweringSubstitution_difference (e : WeightedLoweringAut w R) (hw : Monotone w)
    (i : Fin d) (x y : Fin d → R) (hxy : ∀ j, j < i → x j = y j) :
    polynomialSubstitutionPoint e.val.toAlgHom x i - x i =
      polynomialSubstitutionPoint e.val.toAlgHom y i - y i := by
  have h := aeval_eq_of_weightedSupportLT (e.property i) x y (fun j hj =>
    hxy j (lt_of_not_ge (fun hij => (not_le_of_gt hj) (hw hij))))
  change aeval x (e.val (X i)) - x i = aeval y (e.val (X i)) - y i
  simpa only [map_sub, aeval_X] using h

theorem weightedLoweringSubstitution_prefix (e : WeightedLoweringAut w R) (hw : Monotone w)
    (i : Fin d) (x y : Fin d → R) (hxy : ∀ j, j < i → x j = y j)
    (j : Fin d) (hj : j < i) :
    polynomialSubstitutionPoint e.val.toAlgHom x j =
      polynomialSubstitutionPoint e.val.toAlgHom y j := by
  have h := weightedLoweringSubstitution_difference e hw j x y
    (fun k hk => hxy k (hk.trans hj))
  rw [hxy j hj] at h
  simpa only [sub_add_cancel] using congrArg (fun z => z + y j) h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem real_adapted_coordinate_degree (e : Basis ι ℚ L) (omega : ι → ℕ)
    (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))
    {w : σ → ℕ} (p : F.realification.PolynomialOrbit w) (j : ι) :
    coordinate ((e.baseChange ℝ).coord j).toAddMonoidHom p.log ∈
      weightedSupportLE w (omega j) := by
  rw [mem_weightedSupportLE_iff, scalar_weightedDegree_le_iff]
  intro α hα
  rw [coeff_coordinate]
  change (e.baseChange ℝ).repr (coefficients p.log α) j = 0
  have hm := (F.realification.adapted_iff_coefficients w p.log).mp p.adapted α
  change coefficients p.log α ∈ (F.realLayer (Finsupp.weight w α)).toSubmodule at hm
  rw [F.realLayer_eq_span_basis e _ _ (hlayer _), (e.baseChange ℝ).mem_span_image] at hm
  by_contra h
  exact (not_le_of_gt hα) (hm (Finsupp.mem_support_iff.mpr h))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

include hlayer

theorem real_scaled_adapted_basis_mem (B : ℝ) (j : Fin d) :
    B • (e.baseChange ℝ) j ∈ F.realification.layer (omega j) := by
  change B • (e.baseChange ℝ) j ∈ (F.realLayer (omega j)).toSubmodule
  rw [F.realLayer_eq_span_basis e _ _ (hlayer _)]
  exact Submodule.smul_mem _ B (Submodule.subset_span ⟨j, by simp, rfl⟩)

noncomputable def orderedSlotFactor (B : ℝ) (i j : Fin d) :
    F.realification.PolynomialOrbit (patchVariableWeight (σ := σ) omega i) := by
  classical
  exact if h : j.val < i.val then
    polynomialOrbitOfLog
      (monomial (Finsupp.single (Sum.inr (⟨j.val, h⟩ : Fin i.val)) 1)
        (B • (e.baseChange ℝ) j)) (by
      apply (F.realification.mem_adaptedSubmodule _ _).mp
      apply F.realification.monomial_mem_adaptedSubmodule
      simpa only [Finsupp.weight_single, one_smul, patchVariableWeight,
        Sum.elim_inr, earlierSlot, Fin.eta] using
        F.real_scaled_adapted_basis_mem e omega hlayer B j)
  else 1

noncomputable def orderedSlotOrbit (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) (i : Fin d) :
    F.realification.PolynomialOrbit (patchVariableWeight (σ := σ) omega i) :=
  F.realification.constantPolynomialOrbit _ a *
    F.realification.polynomialOrbitSubstitute
      (w := fun _ : σ => 1) (v := patchVariableWeight omega i)
      (fun x => (MvPolynomial.X (Sum.inl x) : MvPolynomial (σ ⊕ Fin i.val) ℚ))
      (by
        intro x
        simpa only [patchVariableWeight, Sum.elim_inl] using
          (weightedSupportLE_X (R := ℚ) (patchVariableWeight (σ := σ) omega i) (Sum.inl x))) p *
    ((List.finRange d).map (F.orderedSlotFactor e omega hlayer B i)).prod

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

include hlayers hP

theorem real_ofCoordinates_adapted :
    F.realification.Adapted v (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) := by
  classical
  apply (F.realification.adapted_iff_coefficients v _).mpr
  intro α
  change coefficients (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) α ∈
    (F.realLayer (Finsupp.weight v α)).toSubmodule
  rw [coefficients_ofCoordinates, F.realLayer_eq_span_basis b _ _ (hlayers _)]
  apply Submodule.sum_mem
  intro i _
  by_cases hα : Finsupp.weight v α ≤ ω i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hα, rfl⟩)
  · have hc : (P i).coeff α = 0 := by
      by_contra hne
      exact hα (hP i (MvPolynomial.mem_support_iff.mpr hne))
    rw [hc, zero_smul]
    exact Submodule.zero_mem _

noncomputable def realCoordinatePolynomialOrbit : F.realification.PolynomialOrbit v :=
  polynomialOrbitOfLog (ofCoordinates (R := ℚ) (b.baseChange ℝ) P)
    (F.real_ofCoordinates_adapted b ω hlayers v P hP)

@[simp] theorem realCoordinatePolynomialOrbit_log :
    (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log =
      ofCoordinates (R := ℚ) (b.baseChange ℝ) P := rfl

@[simp] theorem realCoordinatePolynomialOrbit_coordinate (i : ι) :
    coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom
      (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log = P i :=
  coordinate_ofCoordinates (b.baseChange ℝ) P i

theorem realCoordinatePolynomialOrbit_eval_coordinates (u : σ → ℝ) (i : ι) :
    (b.baseChange ℝ).repr
      (F.realification.polynomialOrbitRealEval v u
        (F.realCoordinatePolynomialOrbit b ω hlayers v P hP)).coord i =
      MvPolynomial.eval u (P i) := by
  change (b.baseChange ℝ).coord i
    (eval₂ u (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log) = _
  rw [coordinate_eval₂, realCoordinatePolynomialOrbit_coordinate]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

noncomputable def orderedPolynomialSlots (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) : PolynomialSlots σ d omega where
  center i := MvPolynomial.C (-1 / B) *
    coordinate ((e.baseChange ℝ).coord i).toAddMonoidHom
      (F.orderedSlotOrbit e omega hlayer B a p i).log
  degree i := by
    simpa only [zero_add] using weightedSupportLE_mul
      (weightedSupportLE_C (patchVariableWeight omega i) 0 (-1 / B))
      (F.real_adapted_coordinate_degree e omega hlayer
        (F.orderedSlotOrbit e omega hlayer B a p i) i)

noncomputable def orderedPolynomialPatch (hpos : ∀ i, 1 ≤ omega i)
    (hmax : ∀ i, omega i ≤ s) (hmono : Monotone omega) (B : ℝ)
    (a : F.realification.Group) (p : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (Phi : PatchKernel d) : PolynomialPatch σ s d where
  weight := omega
  weight_pos := hpos
  weight_le := hmax
  weight_mono := hmono
  form := F.orderedPolynomialSlots e omega hlayer B a p
  kernel := Phi

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realExtendedSymbolMap :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.polynomialSymbolMap w)

theorem realSymbolOfPolynomial_realAdaptedPolynomialMap
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w (F.realAdaptedPolynomialMap w x) =
      F.realExtendedSymbolMap w x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
    ext z
    rw [F.realSymbolOfPolynomial_coordinate, F.realAdaptedPolynomialMap_coefficient_tmul]
    change (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
        (a ⊗ₜ[ℚ] F.polynomialSymbolMap w p) z
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, F.polynomialSymbolBasis_repr_map]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realPolynomialSymbolMap :
    F.realification.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w where
  toLinearMap := (F.realSymbolOfPolynomial b ω hlayers w).comp
    (F.realification.adaptedLieSubalgebra w).incl.toLinearMap
  map_lie' {p q} := by
    change F.realSymbolOfPolynomial b ω hlayers w (↑⁅p, q⁆) =
      ⁅F.realSymbolOfPolynomial b ω hlayers w p, F.realSymbolOfPolynomial b ω hlayers w q⁆
    obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers p
    obtain ⟨y, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers q
    rw [← (F.realAdaptedPolynomialTensor w).map_lie x y]
    simp only [F.realAdaptedPolynomialTensor_coe, F.realSymbolOfPolynomial_realAdaptedPolynomialMap]
    exact (F.realExtendedSymbolMap w).map_lie x y

@[simp] theorem realPolynomialSymbolMap_apply (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hlayers w p = F.realSymbolOfPolynomial b ω hlayers w p := rfl

@[simp] theorem realPolynomialSymbolMap_representative (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolMap b ω hlayers w (F.realAdaptedSymbolRepresentative b ω hlayers w x) = x := by
  rw [F.realPolynomialSymbolMap_apply, F.realAdaptedSymbolRepresentative_coe,
    F.realSymbolOfPolynomial_representative]

theorem realPolynomialSymbolMap_surjective :
    Function.Surjective (F.realPolynomialSymbolMap b ω hlayers w) :=
  fun x => ⟨F.realAdaptedSymbolRepresentative b ω hlayers w x,
    F.realPolynomialSymbolMap_representative b ω hlayers w x⟩

theorem realPolynomialSymbolMap_eq_zero_iff (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hlayers w p = 0 ↔
      F.realification.polynomialSymbolMap w p = 0 := by
  rw [F.realPolynomialSymbolMap_apply, F.realSymbolOfPolynomial_eq_zero_iff,
    F.realification.polynomialSymbolMap_eq_zero_iff]

noncomputable def realPolynomialSymbolHom :
    (F.realification.adaptedPolynomialFiltration w).Group →* F.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.realPolynomialSymbolMap b ω hlayers w)

@[simp] theorem realPolynomialSymbolHom_coord
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    (F.realPolynomialSymbolHom b ω hlayers w g).coord =
      F.realPolynomialSymbolMap b ω hlayers w g.coord := rfl

noncomputable def realPolynomialSymbolLift (g : F.RealPolynomialSymbolGroup w) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  ⟨F.realAdaptedSymbolRepresentative b ω hlayers w g.coord⟩

@[simp] theorem realPolynomialSymbolHom_lift (g : F.RealPolynomialSymbolGroup w) :
    F.realPolynomialSymbolHom b ω hlayers w (F.realPolynomialSymbolLift b ω hlayers w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp only [F.realPolynomialSymbolHom_coord, realPolynomialSymbolLift,
    F.realPolynomialSymbolMap_representative]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))
  (Λ : Subgroup F.Group) [MetricSpace (F.realification.Group ⧸ Λ.map realificationHom)]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)

theorem repr_coefficients_ofCoordinates (α : σ →₀ ℕ) (i : ι) :
    (b.baseChange ℝ).repr (coefficients
      (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) α) i = (P i).coeff α := by
  exact congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α)
    (coordinate_ofCoordinates (R := ℚ) (b.baseChange ℝ) P i)

theorem realSymbolRepresentative_ofCoordinates :
    F.realSymbolRepresentative b ω hlayers v
      (F.realSymbolOfPolynomial b ω hlayers v
        (ofCoordinates (R := ℚ) (b.baseChange ℝ) P)) =
      ofCoordinates (R := ℚ) (b.baseChange ℝ)
        (fun i => weightedHomogeneousComponent v (ω i) (P i)) := by
  classical
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight v α = ω i
  · have hc := F.realSymbolRepresentative_coefficient b ω hlayers v
      (F.realSymbolOfPolynomial b ω hlayers v
        (ofCoordinates (R := ℚ) (b.baseChange ℝ) P)) ⟨(α, i), h⟩
    have hs := F.realSymbolOfPolynomial_coordinate b ω hlayers v
      (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) ⟨(α, i), h⟩
    rw [hc, hs, repr_coefficients_ofCoordinates, repr_coefficients_ofCoordinates,
      coeff_weightedHomogeneousComponent, if_pos h]
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers v _ α i h,
      repr_coefficients_ofCoordinates, coeff_weightedHomogeneousComponent, if_neg h]

theorem realSymbolOfPolynomial_ofCoordinates_top :
    F.realSymbolOfPolynomial b ω hlayers v
      (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) =
    F.realSymbolOfPolynomial b ω hlayers v
      (ofCoordinates (R := ℚ) (b.baseChange ℝ)
        (fun i => weightedHomogeneousComponent v (ω i) (P i))) := by
  rw [← F.realSymbolRepresentative_ofCoordinates b ω hlayers v P]
  exact (F.realSymbolOfPolynomial_representative b ω hlayers v _).symm

variable (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

end NilpotentLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedGradedCalculus
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

abbrev FilteredFirstJet := F.adaptedLieSubalgebra w ⧸ F.shiftedPolynomialIdeal w 2

noncomputable def filteredFirstJetMap : F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.FilteredFirstJet w :=
  lieQuotientMap (F.shiftedPolynomialIdeal w 2)

theorem filteredFirstJetMap_surjective : Function.Surjective (F.filteredFirstJetMap w) :=
  lieQuotientMap_surjective _

theorem filteredFirstJetMap_eq_zero_iff (p : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetMap w p = 0 ↔ ∀ α, coefficients p.val α ∈ F.layer (Finsupp.weight w α + 2) :=
  lieQuotientMap_eq_zero _ p

theorem filteredFirstJetMap_eq_iff (p q : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetMap w p = F.filteredFirstJetMap w q ↔
      ∀ α, coefficients (p.val - q.val) α ∈ F.layer (Finsupp.weight w α + 2) := by
  rw [← sub_eq_zero, ← map_sub, F.filteredFirstJetMap_eq_zero_iff]
  rfl

noncomputable def filteredFirstJetSymbol : F.FilteredFirstJet w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  { toLinearMap := (F.shiftedPolynomialIdeal w 2).toSubmodule.liftQ
      (F.polynomialSymbolMap w).toLinearMap (by
        intro p hp
        apply (F.polynomialSymbolMap_eq_zero_iff w p).mpr
        exact F.shiftedAdaptedSubmodule_antitone w (by decide : 1 ≤ 2) hp)
    map_lie' {x y} := by
      obtain ⟨p, rfl⟩ := F.filteredFirstJetMap_surjective w x
      obtain ⟨q, rfl⟩ := F.filteredFirstJetMap_surjective w y
      change F.polynomialSymbolMap w ⁅p, q⁆ = ⁅F.polynomialSymbolMap w p, F.polynomialSymbolMap w q⁆
      exact (F.polynomialSymbolMap w).map_lie p q }

@[simp] theorem filteredFirstJetSymbol_map (p : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetSymbol w (F.filteredFirstJetMap w p) = F.polynomialSymbolMap w p := rfl

theorem filteredFirstJet_lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ (F.FilteredFirstJet w) (F.FilteredFirstJet w) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficients_pderiv (i : σ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L p) α =
      (α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q x =>
    rw [LinearMap.rTensor_tmul]
    rw [coefficients_tmul, coefficients_tmul]
    change (MvPolynomial.pderiv i q).coeff α • x =
      (α i + 1 : ℚ) • (q.coeff (α + Finsupp.single i 1) • x)
    rw [MvPolynomial.coeff_pderiv, smul_smul]
    congr 1
    ring
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq, smul_add]

theorem coefficients_directionalDerivative [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (directionalDerivative h p) α =
      ∑ i, h i • ((α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1)) := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, coefficients_pderiv]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem directionalDerivative_mem_shifted [Fintype σ] (h : σ → ℚ) (k : ℕ)
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k) :
    directionalDerivative h p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) (k + 1) := by
  intro α
  rw [coefficients_directionalDerivative]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  have hi := hp (α + Finsupp.single i 1)
  simpa only [map_add, Finsupp.weight_single, one_smul, Nat.add_right_comm, Nat.add_assoc] using hi

theorem directionalDerivative_mem_next [Fintype σ] (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    directionalDerivative h p.val ∈ F.shiftedAdaptedSubmodule (fun _ => 1) 1 := by
  apply F.directionalDerivative_mem_shifted h 0
  intro α
  simpa only [Nat.add_zero] using p.property α

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def taylorRemainder (h : σ → ℚ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ L :=
  (scalarTaylorRemainder h).rTensor L

theorem taylorRemainder_apply (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    taylorRemainder h p = translate h p - p - directionalDerivative h p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q x =>
    change scalarTaylorRemainder h q ⊗ₜ[ℚ] x = _
    rw [scalarTaylorRemainder_apply, TensorProduct.sub_tmul, TensorProduct.sub_tmul,
      translate_tmul, directionalDerivative_tmul, scalarDirectionalDerivative_apply, TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    abel

theorem coefficients_taylorRemainder_monomial (h : σ → ℚ) (α β : σ →₀ ℕ) (x : L) :
    coefficients (taylorRemainder h (monomial α x)) β =
      (scalarTaylorRemainder h (MvPolynomial.monomial α 1)).coeff β • x := by
  change coefficients (scalarTaylorRemainder h (MvPolynomial.monomial α 1) ⊗ₜ[ℚ] x) β = _
  exact coefficients_tmul _ _ _

theorem coefficients_taylorRemainder (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (taylorRemainder h p) α = ∑ β ∈ (coefficients p).support,
      (scalarTaylorRemainder h (MvPolynomial.monomial β 1)).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, coefficients_taylorRemainder_monomial]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem taylorRemainder_mem_shifted (h : σ → ℚ) (k : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k) :
    translate h p - p - directionalDerivative h p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) (k + 2) := by
  rw [← taylorRemainder_apply]
  intro α
  rw [coefficients_taylorRemainder]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (scalarTaylorRemainder h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ (hp β)
    have hd := scalarTaylorRemainder_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 2 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    omega

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def adaptedDirectionalDerivative :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  ((directionalDerivative h).comp (F.adaptedLieSubalgebra (fun _ => 1)).incl.toLinearMap).codRestrict
    (F.adaptedLieSubalgebra (fun _ => 1)).toSubmodule (by
      intro p α
      exact F.antitone (Nat.le_succ _) (F.directionalDerivative_mem_next h p α))

@[simp] theorem adaptedDirectionalDerivative_coe (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (F.adaptedDirectionalDerivative h p : VectorPolynomial σ ℚ L) = directionalDerivative h p.val := rfl

theorem adaptedDirectionalDerivative_mem_shifted (k : ℕ)
    {p : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hp : p ∈ F.shiftedPolynomialIdeal (fun _ => 1) k) :
    F.adaptedDirectionalDerivative h p ∈ F.shiftedPolynomialIdeal (fun _ => 1) (k + 1) :=
  F.directionalDerivative_mem_shifted h k hp

noncomputable def symbolFirstDerivative :
    F.PolynomialSymbol (fun _ : σ => 1) →ₗ[ℚ] F.FilteredFirstJet (fun _ : σ => 1) :=
  (F.shiftedAdaptedIdeal (fun _ => 1)).toSubmodule.liftQ
    ((F.filteredFirstJetMap (fun _ => 1)).toLinearMap.comp (F.adaptedDirectionalDerivative h)) (by
      intro p hp
      exact (F.filteredFirstJetMap_eq_zero_iff (fun _ => 1) _).mpr
        (F.adaptedDirectionalDerivative_mem_shifted h 1 hp))

@[simp] theorem symbolFirstDerivative_map (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p) =
      F.filteredFirstJetMap (fun _ => 1) (F.adaptedDirectionalDerivative h p) := rfl

theorem filteredFirstJet_translate (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1)
      ⟨translate h p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
        (F.adapted_translate (fun _ => 1) (by simp) h
          ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩ =
      F.filteredFirstJetMap (fun _ => 1) p +
        F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p) := by
  rw [F.symbolFirstDerivative_map, ← map_add]
  apply (F.filteredFirstJetMap_eq_iff (fun _ => 1) _ _).mpr
  have hp : p.val ∈ F.shiftedAdaptedSubmodule (fun _ => 1) 0 := by
    intro α
    simpa only [Nat.add_zero] using p.property α
  have hr := F.taylorRemainder_mem_shifted h 0 hp
  change ∀ α, coefficients (translate h p.val - (p.val + directionalDerivative h p.val)) α ∈ _
  rw [show translate h p.val - (p.val + directionalDerivative h p.val) =
      translate h p.val - p.val - directionalDerivative h p.val by abel]
  exact hr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem filteredFirstJet_normalizedShift [Fintype σ] (h : σ → ℚ) (a b : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1)
      ⟨normalizedShiftLog s h a b p.val,
        (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
          (F.normalizedShiftLog_adapted (fun _ => 1) (by simp) h a b
            ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩ =
      lieBCH s (F.filteredFirstJetMap (fun _ => 1) (F.adaptedConstant (fun _ => 1) a))
        (lieBCH s (F.filteredFirstJetMap (fun _ => 1) p +
          F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p))
            (F.filteredFirstJetMap (fun _ => 1) (F.adaptedConstant (fun _ => 1) b))) := by
  let q : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
    ⟨translate h p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
      (F.adapted_translate (fun _ => 1) (by simp) h
        ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩
  have he : (⟨normalizedShiftLog s h a b p.val,
        (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
          (F.normalizedShiftLog_adapted (fun _ => 1) (by simp) h a b
            ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩ :
      F.adaptedLieSubalgebra (fun _ : σ => 1)) =
      lieBCH s (F.adaptedConstant (fun _ => 1) a)
        (lieBCH s q (F.adaptedConstant (fun _ => 1) b)) := by
    apply Subtype.ext
    change normalizedShiftLog s h a b p.val =
      (F.adaptedLieSubalgebra (fun _ : σ => 1)).incl
        (lieBCH s (F.adaptedConstant (fun _ => 1) a) (lieBCH s q (F.adaptedConstant (fun _ => 1) b)))
    rw [map_lieBCH, map_lieBCH]
    rfl
  rw [he, map_lieBCH, map_lieBCH]
  have ht : F.filteredFirstJetMap (fun _ => 1) q = F.filteredFirstJetMap (fun _ => 1) p +
      F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p) := F.filteredFirstJet_translate h p
  rw [ht]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def adaptedPolynomialJet (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    DualGroup (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot :=
  ⟨dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p)⟩

@[simp] theorem adaptedPolynomialJet_base (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualBaseLinear (F.adaptedPolynomialJet h p).coord = p := by
  change dualBaseLinear (dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p)) = p
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem adaptedPolynomialJet_tangent (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualTangentLinear (F.adaptedPolynomialJet h p).coord = F.adaptedDirectionalDerivative h p := by
  change dualTangentLinear (dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p)) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem adaptedPolynomialJet_baseHom (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualBaseHom (F.adaptedPolynomialJet h p) =
      (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) := by
  apply NilpotentLieBCHGroup.ext
  exact F.adaptedPolynomialJet_base h p

noncomputable def normalizedShiftAdapted (a b : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  ⟨normalizedShiftLog s h a b p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
    (F.normalizedShiftLog_adapted (fun _ => 1) (by simp) h a b
      ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩

noncomputable def normalizedRelativeLog (e m : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)

noncomputable def adaptedLogDerivative (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedLieSubalgebra (fun _ : σ => 1) := dualLogDerivative (F.adaptedPolynomialJet h p)

theorem filteredFirstJet_normalizedRelativeLog (e m : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1) (F.normalizedRelativeLog h e m p) =
      F.filteredFirstJetMap (fun _ => 1)
        (F.adaptedLogDerivative h p - F.adaptedConstant (fun _ => 1) e -
          dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
            (F.adaptedConstant (fun _ => 1) m)) := by
  have hbracket : ∀ x ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
      ∀ y ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
        ⁅x, y⁆ ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
    intro x hx y hy
    exact F.shiftedPolynomialIdeal_lie_mem (fun _ => 1) (i := 1) (j := 1) hx hy
  have hz : dualTangentLinear (F.adaptedPolynomialJet h p).coord ∈
      F.shiftedPolynomialIdeal (fun _ : σ => 1) 1 := by
    rw [F.adaptedPolynomialJet_tangent]
    exact F.directionalDerivative_mem_next h p
  have hid := dualBCH_insertion_quotient
    (F.shiftedPolynomialIdeal (fun _ : σ => 1) 1) (F.shiftedPolynomialIdeal (fun _ : σ => 1) 2)
    hbracket (F.adaptedPolynomialJet h p)
    (F.adaptedConstant (fun _ => 1) e) (F.adaptedConstant (fun _ => 1) m) hz
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) e)
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) m)
  rw [F.adaptedPolynomialJet_base, F.adaptedPolynomialJet_tangent,
    F.adaptedPolynomialJet_baseHom] at hid
  change F.filteredFirstJetMap (fun _ => 1)
    (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)) = _
  rw [map_lieBCH, map_neg]
  have hn := F.filteredFirstJet_normalizedShift h (-e) (-m) p
  change F.filteredFirstJetMap (fun _ => 1) (F.normalizedShiftAdapted h (-e) (-m) p) = _ at hn
  rw [hn, F.symbolFirstDerivative_map]
  have hc (a : L) : F.adaptedConstant (fun _ : σ => 1) (-a) =
      -F.adaptedConstant (fun _ : σ => 1) a := (F.adaptedConstantLieHom (fun _ => 1)).map_neg a
  rw [hc e, hc m, map_neg, map_neg,
    ← lieBCH_assoc (F.filteredFirstJet_lowerCentralSeries_eq_bot (fun _ : σ => 1))]
  rw [map_add] at hid
  exact hid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem adaptedDirectionalDerivative_lie (p q : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedDirectionalDerivative h ⁅p, q⁆ =
      ⁅F.adaptedDirectionalDerivative h p, q⁆ + ⁅p, F.adaptedDirectionalDerivative h q⁆ := by
  apply Subtype.ext
  exact directionalDerivative_lie h p.val q.val

noncomputable def adaptedPolynomialJetLie :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ⁅ℚ⁆
      DualLieAlgebra (F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toLinearMap := dualConstantLie.toLinearMap +
    dualInfinitesimal.comp (F.adaptedDirectionalDerivative h)
  map_lie' {p q} := by
    change dualConstantLie ⁅p, q⁆ + dualInfinitesimal (F.adaptedDirectionalDerivative h ⁅p, q⁆) =
      ⁅dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p),
        dualConstantLie q + dualInfinitesimal (F.adaptedDirectionalDerivative h q)⁆
    apply dual_ext
    · simp only [map_add, dualBaseLinear_constant,
        dualBaseLinear_infinitesimal, add_zero, dualBaseLinear_lie]
    · simp only [map_add, dualTangentLinear_constant,
        dualTangentLinear_infinitesimal, zero_add, dualTangentLinear_lie,
        dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]
      rw [F.adaptedDirectionalDerivative_lie]
      exact add_comm _ _

noncomputable def adaptedPolynomialJetHom :
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group →*
      DualGroup (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.adaptedPolynomialJetLie h)

@[simp] theorem adaptedPolynomialJetHom_apply
    (P : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedPolynomialJetHom h P = F.adaptedPolynomialJet h P.coord := rfl

theorem adaptedLogDerivative_mul
    (P Q : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedLogDerivative h (P * Q).coord =
      F.adaptedLogDerivative h P.coord + dualAdjoint P (F.adaptedLogDerivative h Q.coord) := by
  change dualLogDerivative (F.adaptedPolynomialJetHom h (P * Q)) = _
  rw [map_mul, dualLogDerivative_mul, F.adaptedPolynomialJetHom_apply,
    F.adaptedPolynomialJet_baseHom]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_tangent (x : L) :
    dualLogDerivative (hnil := hnil) (dualTangentElement x) = x := by
  simpa only [map_one, mul_one] using
    dualLogDerivative_tangent_mul_constant x (1 : NilpotentLieBCHGroup L s hnil)

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedLogDerivative_constant (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hp : coefficients p.val 0 = 0) :
    coefficients (F.adaptedLogDerivative h p).val 0 =
      coefficients (directionalDerivative h p.val) 0 := by
  let φ : F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ⁅ℚ⁆ L :=
    (evalLie (0 : σ → ℚ)).comp (F.adaptedLieSubalgebra (fun _ => 1)).incl
  have hφ (q : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
      φ q = coefficients q.val 0 := eval_zero_eq_coefficient q.val
  have hjet : dualLinearLift φ φ.toLinearMap (F.adaptedPolynomialJet h p).coord =
      (dualTangentElement (hnil := F.lowerCentralSeries_eq_bot)
        (φ (F.adaptedDirectionalDerivative h p))).coord := by
    rw [dualLinearLift_apply, F.adaptedPolynomialJet_base, F.adaptedPolynomialJet_tangent]
    change dualConstantLie (φ p) + dualInfinitesimal (φ (F.adaptedDirectionalDerivative h p)) = _
    rw [hφ p, hp, map_zero, zero_add]
    rfl
  have he := dualLinearLift_logDerivative_eq F.lowerCentralSeries_eq_bot
    (⊤ : LieIdeal ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1))) φ φ.toLinearMap
    (fun x y _ => φ.map_lie x y) (F.adaptedPolynomialJet h p) (by trivial)
    (dualTangentElement (φ (F.adaptedDirectionalDerivative h p))) hjet
  rw [dualLogDerivative_tangent] at he
  change φ (F.adaptedLogDerivative h p) = φ (F.adaptedDirectionalDerivative h p) at he
  simpa only [hφ, F.adaptedDirectionalDerivative_coe] using he

theorem adaptedLogDerivative_constant_unit [DecidableEq σ] (i : σ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hp : coefficients p.val 0 = 0) :
    coefficients (F.adaptedLogDerivative (Pi.single i 1) p).val 0 =
      coefficients p.val (Finsupp.single i 1) := by
  classical
  rw [F.adaptedLogDerivative_constant _ p hp, coefficients_directionalDerivative]
  simp [Pi.single_apply]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedDirectionalTangent
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℚ) →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) where
  toFun h := F.adaptedDirectionalDerivative h p
  map_add' h k := Subtype.ext (directionalDerivative_direction_add h k p.val)
  map_smul' r h := Subtype.ext (directionalDerivative_direction_smul r h p.val)

noncomputable def adaptedLogDerivativeLinear
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℚ) →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  (dualLogarithmicDifferential
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot) p).comp
      (F.adaptedDirectionalTangent p)

@[simp] theorem adaptedLogDerivativeLinear_apply
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℚ) :
    F.adaptedLogDerivativeLinear p h = F.adaptedLogDerivative h p := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem gradedPieceProjection_lie {i j : ℕ} {u v : L}
    (hu : u ∈ F.layer i) (hv : v ∈ F.layer j) :
    F.gradedPieceProjection b ω hlayers (i + j) ⁅u, v⁆ =
      ⁅F.gradedPieceProjection b ω hlayers i u, F.gradedPieceProjection b ω hlayers j v⁆ := by
  have hi := F.gradedPieceProjection_eq_pieceMap b ω hlayers i ⟨u, hu⟩
  have hj := F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩
  have hij := F.gradedPieceProjection_eq_pieceMap b ω hlayers (i + j) ⟨⁅u, v⁆, F.lie_mem hu hv⟩
  change F.gradedPieceProjection b ω hlayers i u = _ at hi
  change F.gradedPieceProjection b ω hlayers j v = _ at hj
  change F.gradedPieceProjection b ω hlayers (i + j) ⁅u, v⁆ = _ at hij
  rw [hi, hj, hij, F.associatedGradedPieceMap_lie]

theorem shiftedGradedPolynomial_lie (w : σ → ℕ) {i j : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w i) (hq : q ∈ F.shiftedAdaptedSubmodule w j) :
    F.shiftedGradedPolynomial b ω hlayers w (i + j) ⁅p, q⁆ =
      ⁅F.shiftedGradedPolynomial b ω hlayers w i p, F.shiftedGradedPolynomial b ω hlayers w j q⁆ := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, sum_lie_sum, map_sum, lie_monomial, F.shiftedGradedPolynomial_monomial]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  have hdeg : Finsupp.weight w (α + β) + (i + j) =
      (Finsupp.weight w α + i) + (Finsupp.weight w β + j) := by
    rw [map_add]
    omega
  rw [hdeg, F.gradedPieceProjection_lie b ω hlayers (hp α) (hq β)]

theorem shiftedGradedPolynomial_directionalDerivative [Fintype σ] (h : σ → ℚ)
    (k : ℕ) (p : VectorPolynomial σ ℚ L) :
    F.shiftedGradedPolynomial b ω hlayers (fun _ : σ => 1) (k + 1) (directionalDerivative h p) =
      directionalDerivative h (F.shiftedGradedPolynomial b ω hlayers (fun _ : σ => 1) k p) := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.shiftedGradedPolynomial_coefficient, coefficients_directionalDerivative,
    coefficients_directionalDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, F.shiftedGradedPolynomial_coefficient]
  simp only [map_add, Finsupp.weight_single, one_smul, Nat.add_right_comm, Nat.add_assoc]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareSymbolProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def filteredFirstJetConstant : F.FilteredFirstJet w →ₗ[ℚ] L ⧸ F.layer 2 :=
  (F.shiftedPolynomialIdeal w 2).toSubmodule.liftQ
    ((F.layer 2).mkQ.comp (F.adaptedCoefficientMap w 0)) (by
      intro p hp
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change coefficients p.val 0 ∈ F.layer 2
      have hc : coefficients p.val 0 ∈ F.layer (Finsupp.weight w 0 + 2) := hp 0
      simpa only [map_zero, Nat.zero_add] using hc)

@[simp] theorem filteredFirstJetConstant_map (p : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetConstant w (F.filteredFirstJetMap w p) =
      (F.layer 2).mkQ (coefficients p.val 0) := rfl

variable (hw : ∀ i, 0 < w i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def squareSndSymbolMap : F.squareFiltration.PolynomialSymbol w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  F.squareFiltration.filteredPolynomialSymbolMap F F.squareSnd (fun _ _ hx => hx.2.1) w

theorem squareSndSymbolMap_map_eq_zero_iff (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.squareSndSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) = 0 ↔
      ∀ α, (coefficients r.val α).val.2 ∈ F.layer (Finsupp.weight w α + 1) := by
  change F.polynomialSymbolMap w
    (F.squareFiltration.filteredPolynomialMap F F.squareSnd (fun _ _ hx => hx.2.1) w r) = 0 ↔ _
  rw [F.polynomialSymbolMap_eq_zero_iff]
  change (∀ α, coefficients (VectorPolynomial.map F.squareSnd.toLinearMap r.val) α ∈
    F.layer (Finsupp.weight w α + 1)) ↔ _
  simp only [coefficients_map]
  rfl

variable (hw : ∀ i, 0 < w i)

theorem squareSndSymbolMap_relative (p : F.normalizedRelativeSubmodule w) :
    F.squareSndSymbolMap w (F.relativeSquareSymbolMap w hw p) = 0 := by
  apply (F.squareSndSymbolMap_map_eq_zero_iff w (F.relativeSquareLift w hw p)).mpr
  intro α
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.2 ∈ _
  rw [F.relativeSquarePolynomial_coefficient]
  exact (F.layer _).zero_mem

theorem relativeSquareSymbolMap_range :
    LinearMap.range (F.relativeSquareSymbolMap w hw) = (F.squareSndSymbolMap w).ker.toSubmodule := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact F.squareSndSymbolMap_relative w hw p
  · intro x hx
    obtain ⟨r, rfl⟩ := F.squareFiltration.polynomialSymbolMap_surjective w x
    have hs : ∀ α, (coefficients r.val α).val.2 ∈ F.layer (Finsupp.weight w α + 1) :=
      (F.squareSndSymbolMap_map_eq_zero_iff w r).mp hx
    let p : VectorPolynomial σ ℚ L :=
      VectorPolynomial.map F.squareFst.toLinearMap r.val - VectorPolynomial.map F.squareSnd.toLinearMap r.val
    have hc (α : σ →₀ ℕ) : coefficients p α =
        (coefficients r.val α).val.1 - (coefficients r.val α).val.2 := by
      simp only [p, map_sub, Finsupp.sub_apply, coefficients_map]
      rfl
    have hp : ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α + 1) := by
      intro α
      rw [hc]
      exact (r.property α).2.2
    have hpa : p ∈ F.adaptedLieSubalgebra w :=
      fun α => F.antitone (Nat.le_succ _) (hp α)
    have hp0 : coefficients p 0 ∈ F.layer 2 := by
      rw [hc]
      exact (F.mem_squareLieSubalgebra _).mp (coefficients r.val 0).property
    let q : F.normalizedRelativeSubmodule w := ⟨⟨p, hpa⟩, hp, hp0⟩
    refine ⟨q, ?_⟩
    apply (F.squareFiltration.polynomialSymbolMap_eq_iff w (F.relativeSquareLift w hw q) r).mpr
    intro α
    rw [map_sub, Finsupp.sub_apply]
    change (coefficients (F.relativeSquarePolynomial w hw q) α).val - (coefficients r.val α).val ∈
      F.squareLayer (Finsupp.weight w α + 1)
    rw [F.relativeSquarePolynomial_coefficient]
    change (coefficients p α, (0 : L)) - (coefficients r.val α).val ∈ _
    rw [hc]
    have he : ((coefficients r.val α).val.1 - (coefficients r.val α).val.2, (0 : L)) -
        (coefficients r.val α).val = (-(coefficients r.val α).val.2, -(coefficients r.val α).val.2) := by
      apply Prod.ext <;> dsimp <;> abel
    rw [he]
    exact ⟨(F.layer _).neg_mem (hs α), (F.layer _).neg_mem (hs α), by simp⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareSymbolRelative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem relativeSquareSymbol_lie_eq_zero (p q : F.normalizedRelativeSubmodule w) :
    ⁅F.relativeSquareSymbolMap w hw p, F.relativeSquareSymbolMap w hw q⁆ = 0 := by
  have hpq : ⁅p.val, q.val⁆ ∈ F.shiftedPolynomialIdeal w 2 :=
    F.shiftedPolynomialIdeal_lie_mem w (i := 1) (j := 1) p.property.1 q.property.1
  have hpq0 : coefficients ⁅p.val, q.val⁆.val 0 ∈ F.layer 2 := by
    have hh := hpq 0
    change coefficients ⁅p.val, q.val⁆.val 0 ∈ F.layer (Finsupp.weight w 0 + 2) at hh
    rw [map_zero, Nat.zero_add] at hh
    exact hh
  let r : F.normalizedRelativeSubmodule w :=
    ⟨⁅p.val, q.val⁆, F.shiftedPolynomialIdeal_antitone w (by decide : 1 ≤ 2) hpq, hpq0⟩
  have he : ⁅F.relativeSquareLift w hw p, F.relativeSquareLift w hw q⁆ =
      F.relativeSquareLift w hw r := by
    apply F.square_polynomial_ext w
    · rw [LieHom.map_lie, F.squareFstPolynomialMap_relative, F.squareFstPolynomialMap_relative,
        F.squareFstPolynomialMap_relative]
    · rw [LieHom.map_lie, F.squareSndPolynomialMap_relative, F.squareSndPolynomialMap_relative,
        F.squareSndPolynomialMap_relative, lie_zero]
  change ⁅F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw p),
    F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw q)⁆ = 0
  rw [← LieHom.map_lie, he]
  exact (F.relativeSquareSymbolMap_eq_zero_iff w hw r).mpr hpq

include hw in
theorem squareSndSymbolKernel_lie_eq_zero {x y : F.squareFiltration.PolynomialSymbol w}
    (hx : F.squareSndSymbolMap w x = 0) (hy : F.squareSndSymbolMap w y = 0) : ⁅x, y⁆ = 0 := by
  have hx' : x ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
    rw [F.relativeSquareSymbolMap_range w hw]
    exact hx
  have hy' : y ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
    rw [F.relativeSquareSymbolMap_range w hw]
    exact hy
  obtain ⟨p, rfl⟩ := hx'
  obtain ⟨q, rfl⟩ := hy'
  exact F.relativeSquareSymbol_lie_eq_zero w hw p q

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

@[simp] theorem squareSndSymbolMap_symbol (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.squareSndSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) =
      F.polynomialSymbolMap w (F.squareSndPolynomialMap w r) := rfl

@[simp] theorem squareSndSymbolMap_diagonal (x : F.PolynomialSymbol w) :
    F.squareSndSymbolMap w (F.squareDiagonalSymbolMap w x) = x := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.squareDiagonalSymbolMap_symbol, F.squareSndSymbolMap_symbol, F.squareSndPolynomialMap_diagonal]

noncomputable def squareSndSymbolHom : F.squareFiltration.PolynomialSymbolGroup w →* F.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.squareSndSymbolMap w)

noncomputable def squareDiagonalSymbolHom : F.PolynomialSymbolGroup w →* F.squareFiltration.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.squareDiagonalSymbolMap w)

@[simp] theorem squareSndSymbolHom_diagonal (g : F.PolynomialSymbolGroup w) :
    F.squareSndSymbolHom w (F.squareDiagonalSymbolHom w g) = g := by
  apply NilpotentLieBCHGroup.ext
  exact F.squareSndSymbolMap_diagonal w g.coord

noncomputable def squareRelativeGroupPart (g : F.squareFiltration.PolynomialSymbolGroup w) :
    F.squareFiltration.PolynomialSymbolGroup w :=
  splitRelativePart (F.squareSndSymbolHom w) (F.squareDiagonalSymbolHom w) g

@[simp] theorem squareRelativeGroupPart_projection (g : F.squareFiltration.PolynomialSymbolGroup w) :
    F.squareSndSymbolHom w (F.squareRelativeGroupPart w g) = 1 :=
  splitRelativePart_projection _ _ (F.squareSndSymbolHom_diagonal w) g

variable (hw : ∀ i, 0 < w i)

end Erdos3.NilpotentLieFiltration

end

end OAI

end


