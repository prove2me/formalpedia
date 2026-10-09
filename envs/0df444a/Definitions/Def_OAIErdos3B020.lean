-- Prove2me | Definitions.Def_OAIErdos3B020
-- name    : OAIErdos3B020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T14:45:53.352387+00:00
-- url     : https://prove2.me/theorems/1c0888ee-f931-4f23-8562-ca31218a619b
-- title:
--   OpenAI Erdős-3 split, definitions bundle 21 of 97
-- statement:
--   Definitions bundle 21 of 97 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B019`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 21 available.
--
--   Modules: `OAI.Erdos3.CyclicCrootSisask.cardinal_ratio_le_exp_momentOrder`, `OAI.Erdos3.CyclicCrootSisask.convolutionMomentOrder`, `OAI.Erdos3.CyclicCrootSisask.convolutionMomentOrder_pos`, `OAI.Erdos3.CyclicCrootSisask.convolution_moment_to_pointwise`, `OAI.Erdos3.CyclicCrootSisask.convolution_period_moment_bound`, `OAI.Erdos3.CyclicCrootSisask.exists_local_almostPeriods`, `OAI.Erdos3.CyclicCrootSisask.exists_local_boosted_triple_almostPeriods`, `OAI.Erdos3.CyclicCrootSisask.exists_local_triple_almostPeriods`, `OAI.Erdos3.CyclicCrootSisask.goodSamples_relative_moment_bound`, `OAI.Erdos3.CyclicCrootSisask.half_card_le_filter_of_sum_le`, `OAI.Erdos3.CyclicCrootSisask.half_pow_spectralIterations_mul_exp_le`, `OAI.Erdos3.CyclicCrootSisask.half_samples_good_input_moment`, `OAI.Erdos3.CyclicCrootSisask.iteratedSetAverage`, `OAI.Erdos3.CyclicCrootSisask.iteratedSetAverage_approx_of_shifts`, `OAI.Erdos3.CyclicCrootSisask.iteratedSetAverage_uniform_error`, `OAI.Erdos3.CyclicCrootSisask.realSetIndicator`, `OAI.Erdos3.CyclicCrootSisask.setAverageTranslate_abs_pow_le`, `OAI.Erdos3.CyclicCrootSisask.setAverageTranslate_abs_pow_le_total`, `OAI.Erdos3.CyclicCrootSisask.setAverageTranslate_approx_of_shifts`, `OAI.Erdos3.CyclicCrootSisask.setAverageTranslate_rightTranslate`, `OAI.Erdos3.CyclicCrootSisask.setAverageTranslate_sub`, `OAI.Erdos3.CyclicCrootSisask.spectralIterationFactor`, `OAI.Erdos3.CyclicCrootSisask.spectralIterations`, `OAI.Erdos3.CyclicCrootSisask.spectralIterations_le`, `OAI.Erdos3.CyclicCrootSisask.spectralIterations_pos`, `OAI.Erdos3.CyclicCrootSisask.sum_realSetIndicator_moment`, `OAI.Erdos3.CyclicCrootSisask.triple_period_moment_bound`, `OAI.Erdos3.PolynomialShearIndex`, `OAI.Erdos3.PolynomialShearLieAlgebra`, `OAI.Erdos3.PolynomialSlots.loweringAt`, `OAI.Erdos3.PolynomialSlots.loweringAtHom`, `OAI.Erdos3.PolynomialSlots.loweringAtHom_lower`, `OAI.Erdos3.PolynomialSlots.loweringAt_aeval`, `OAI.Erdos3.PolynomialSlots.loweringAt_comp_top`, `OAI.Erdos3.PolynomialSlots.loweringHom`, `OAI.Erdos3.PolynomialSlots.loweringHom_X_lower`, `OAI.Erdos3.PolynomialSlots.loweringHom_comp_top`, `OAI.Erdos3.PolynomialSlots.loweringHom_degree`, `OAI.Erdos3.PolynomialSlots.loweringPoint`, `OAI.Erdos3.PolynomialSlots.residualCoordinate`, `OAI.Erdos3.PolynomialSlots.residualCoordinate_degree`, `OAI.Erdos3.PolynomialSlots.residualCoordinate_eval`, `OAI.Erdos3.PolynomialSlots.residualCoordinate_slot_degree`, `OAI.Erdos3.PolynomialSlots.residualCoordinate_sub_topPart_lower`, `OAI.Erdos3.PolynomialSlots.residualHom`, `OAI.Erdos3.PolynomialSlots.residualHom_X`, `OAI.Erdos3.PolynomialSlots.residualHom_sub_topPart_lower`, `OAI.Erdos3.PolynomialSlots.symbolicLogSlot`, `OAI.Erdos3.PolynomialSlots.symbolicLogSlot_degree`, `OAI.Erdos3.PolynomialSlots.symbolicLogSlot_specialization`, `OAI.Erdos3.PolynomialSlots.symbolicShearDifference_pow_degree`, `OAI.Erdos3.PolynomialSlots.symbolicShearDifference_pow_specialization`, `OAI.Erdos3.PolynomialSlots.symbolicShearDifference_specialization`, `OAI.Erdos3.PolynomialSlots.symbolicShearHom`, `OAI.Erdos3.PolynomialSlots.symbolicShearHom_degree`, `OAI.Erdos3.PolynomialSlots.symbolicShearHom_parameter`, `OAI.Erdos3.PolynomialSlots.symbolicShearHom_slot`, `OAI.Erdos3.PolynomialSlots.symbolicShearHom_specialization`, `OAI.Erdos3.PolynomialSlots.topResidualEquiv`, `OAI.Erdos3.PolynomialSlots.topResidualEquiv_X`, `OAI.Erdos3.PolynomialSlots.topResidualEquiv_degree`, `OAI.Erdos3.PolynomialSlots.topResidualEquiv_inverse_degree`, `OAI.Erdos3.PolynomialSlots.topResidualEquiv_lift`, `OAI.Erdos3.PolynomialSlots.topResidualShift_degree`, `OAI.Erdos3.PolynomialSlots.top_factorization_coordinate`, `OAI.Erdos3.PolynomialSlots.top_factorization_residual`, `OAI.Erdos3.PolynomialTranslationGroupOver.action`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionElement`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionElement_X_inl`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionElement_X_inr`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionHom`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionHom_C`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionHom_X_inl`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionHom_X_inr`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionHom_mul`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionHom_one`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionHom_rename`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionMonoidHom`, `OAI.Erdos3.PolynomialTranslationGroupOver.actionMonoidHom_injective`, `OAI.Erdos3.PolynomialTranslationGroupOver.action_eq_of_shape`, `OAI.Erdos3.PolynomialTranslationGroupOver.action_inverse_X_inl_eval`, `OAI.Erdos3.PolynomialTranslationGroupOver.action_inverse_X_inr_eval`, `OAI.Erdos3.PolynomialTranslationGroupOver.algebraic_major_eval_on_subspace`, `OAI.Erdos3.PolynomialTranslationGroupOver.base_inv`, `OAI.Erdos3.PolynomialTranslationGroupOver.base_mul`, `OAI.Erdos3.PolynomialTranslationGroupOver.base_one`, `OAI.Erdos3.PolynomialTranslationGroupOver.existsUnique_action_of_shape`, `OAI.Erdos3.PolynomialTranslationGroupOver.instGroup`, `OAI.Erdos3.PolynomialTranslationGroupOver.instInv`, `OAI.Erdos3.PolynomialTranslationGroupOver.instMul`, `OAI.Erdos3.PolynomialTranslationGroupOver.instOne`, `OAI.Erdos3.PolynomialTranslationGroupOver.map`, `OAI.Erdos3.PolynomialTranslationGroupOver.map_actionHom`, `OAI.Erdos3.PolynomialTranslationGroupOver.map_base`, `OAI.Erdos3.PolynomialTranslationGroupOver.map_polynomial`, `OAI.Erdos3.PolynomialTranslationGroupOver.polynomial_inv`, `OAI.Erdos3.PolynomialTranslationGroupOver.polynomial_mul`, `OAI.Erdos3.PolynomialTranslationGroupOver.polynomial_one`, `OAI.Erdos3.PolynomialTranslationGroupOver.rationalEquiv`, `OAI.Erdos3.PolynomialTranslationGroupOver.rationalEquiv_action`, `OAI.Erdos3.PolynomialTranslationGroupOver.recOn`, `OAI.Erdos3.WeightedLoweringAut.difference_pow_degree`, `OAI.Erdos3.WeightedLoweringAut.difference_pow_lower`, `OAI.Erdos3.algebraicMajorSymbol`, `OAI.Erdos3.algebraic_major_normalized_identity_on_subspace`, `OAI.Erdos3.algebraic_major_normalized_slow_mass`, `OAI.Erdos3.amplificationGain`, `OAI.Erdos3.amplificationResource`, `OAI.Erdos3.constantObservable_integerBox_memberNets`, `OAI.Erdos3.constantObservable_memberNets`, `OAI.Erdos3.eval_integer_polynomial_real`, `OAI.Erdos3.exists_uniformExternalNetScalarBudget`, `OAI.Erdos3.exponentSum_le_positive_weight`, `OAI.Erdos3.floorIntegerPolynomial`, `OAI.Erdos3.floorIntegerPolynomial_add_fractionalCoefficientPolynomial`, `OAI.Erdos3.floorIntegerPolynomial_coeff`, `OAI.Erdos3.fractionalCoefficientPolynomial`, `OAI.Erdos3.fractionalCoefficientPolynomial_bounds`, `OAI.Erdos3.fractionalCoefficientPolynomial_coeff`, `OAI.Erdos3.fractionalCoefficientPolynomial_fourierChar`, `OAI.Erdos3.fractionalCoefficientPolynomial_isWeightedHomogeneous`, `OAI.Erdos3.fractionalCoefficientPolynomial_mass_le`, `OAI.Erdos3.fractionalCoefficientPolynomial_mass_le_card`, `OAI.Erdos3.gainExponent`, `OAI.Erdos3.integerCoefficientPolynomials`, `OAI.Erdos3.integerCoefficientPolynomials_C`, `OAI.Erdos3.integerCoefficientPolynomials_C_iff`, `OAI.Erdos3.integerCoefficientPolynomials_X`, `OAI.Erdos3.integerCoefficientPolynomials_rat_smul`, `OAI.Erdos3.integerCoefficientPolynomials_rename`, `OAI.Erdos3.integerCoefficientPolynomials_rename_iff`, `OAI.Erdos3.integerCoefficientPolynomials_translate`, `OAI.Erdos3.integerCoefficientPolynomials_translate_iff`, `OAI.Erdos3.integerPolynomialDerivation_pow`, `OAI.Erdos3.integerPolynomialDerivation_preserves`, `OAI.Erdos3.integerPolynomialHom_preserves`, `OAI.Erdos3.integerPolynomialTranslationSubgroup`, `OAI.Erdos3.integerWeightedLoweringSubgroup`, `OAI.Erdos3.integerWeightedLowering_difference_pow`, `OAI.Erdos3.integerWeightedLowering_inverse_preserves`, `OAI.Erdos3.integerWeightedLowering_preimage`, `OAI.Erdos3.integerWeightedLowering_preserves`, `OAI.Erdos3.levelCoefficient`, `OAI.Erdos3.localMajorLowerPhase`, `OAI.Erdos3.localMajorLowerPhase_cancellation`, `OAI.Erdos3.localMajorLowerPhase_totalDegree_le`, `OAI.Erdos3.localMajorPhaseCorrelation`, `OAI.Erdos3.mem_integerCoefficientPolynomials`, `OAI.Erdos3.mem_integerCoefficientPolynomials_iff`, `OAI.Erdos3.normalizedMajorLeft`, `OAI.Erdos3.patchParameterSpecialization`, `OAI.Erdos3.patchParameterSpecialization_X_slot`, `OAI.Erdos3.patchParameterSpecialization_eval`, `OAI.Erdos3.patchParameterSpecialization_lower`, `OAI.Erdos3.polynomialDerivationDrop`, `OAI.Erdos3.polynomialDerivationDrop_antitone`, `OAI.Erdos3.polynomialDerivationDrop_bracket`, `OAI.Erdos3.polynomialLoweringLieAlgebra`, `OAI.Erdos3.polynomialShearAction`, `OAI.Erdos3.polynomialShearAssociativeAction`, `OAI.Erdos3.polynomialShearAssociativeAction_positive`, `OAI.Erdos3.polynomialShearBCHEquiv`, `OAI.Erdos3.polynomialShearBasis`, `OAI.Erdos3.polynomialShearBasis_eq_monomial`, `OAI.Erdos3.polynomialShearBasis_mem_layer`, `OAI.Erdos3.polynomialShearBasis_repr`, `OAI.Erdos3.polynomialShearBoundedCoordinates`, `OAI.Erdos3.polynomialShearBoundedCoordinates_injective`, `OAI.Erdos3.polynomialShearCoordinates`, `OAI.Erdos3.polynomialShearDeficit`, `OAI.Erdos3.polynomialShearEnd`, `OAI.Erdos3.polynomialShearEnd_isNilpotent`, `OAI.Erdos3.polynomialShearEnd_mem_drop`, `OAI.Erdos3.polynomialShearEnd_pow_coe`, `OAI.Erdos3.polynomialShearEnd_pow_eq_zero`, `OAI.Erdos3.polynomialShearExp`, `OAI.Erdos3.polynomialShearExpAut`, `OAI.Erdos3.polynomialShearExpAut_apply`, `OAI.Erdos3.polynomialShearExpAut_lieBCH`, `OAI.Erdos3.polynomialShearExpHom`, `OAI.Erdos3.polynomialShearExpOn`, `OAI.Erdos3.polynomialShearExpOn_lieBCH`, `OAI.Erdos3.polynomialShearExpOn_mono`, `OAI.Erdos3.polynomialShearExpOn_mul`, `OAI.Erdos3.polynomialShearExpOn_sum`, `OAI.Erdos3.polynomialShearExp_C`, `OAI.Erdos3.polynomialShearExp_X_of_derivation_eq_C`, `OAI.Erdos3.polynomialShearExp_add`, `OAI.Erdos3.polynomialShearExp_degree`, `OAI.Erdos3.polynomialShearExp_degreeAction`, `OAI.Erdos3.polynomialShearExp_eq_add_of_sq_eq_zero`, `OAI.Erdos3.polynomialShearExp_eq_on`, `OAI.Erdos3.polynomialShearExp_eq_sum`, `OAI.Erdos3.polynomialShearExp_log`, `OAI.Erdos3.polynomialShearExp_mul`, `OAI.Erdos3.polynomialShearExp_sub_lower`, `OAI.Erdos3.polynomialShearExp_weightedSupportLE`, `OAI.Erdos3.polynomialShearFiltration`, `OAI.Erdos3.polynomialShearIndexFintype`, `OAI.Erdos3.polynomialShearLayer`, `OAI.Erdos3.polynomialShearLayer_antitone`, `OAI.Erdos3.polynomialShearLayer_bracket`, `OAI.Erdos3.polynomialShearLayer_one`, `OAI.Erdos3.polynomialShearLayer_span`, `OAI.Erdos3.polynomialShearLayer_terminal`, `OAI.Erdos3.polynomialShearLog`, `OAI.Erdos3.polynomialShearLogDerivation`, `OAI.Erdos3.polynomialShearLogOn`, `OAI.Erdos3.polynomialShearLogOn_leibniz`, `OAI.Erdos3.polynomialShearLogOn_mono`, `OAI.Erdos3.polynomialShearLogOn_sum`, `OAI.Erdos3.polynomialShearLogValue`, `OAI.Erdos3.polynomialShearLogValue_C`, `OAI.Erdos3.polynomialShearLogValue_add`, `OAI.Erdos3.polynomialShearLogValue_eq_on`, `OAI.Erdos3.polynomialShearLogValue_eq_sum`, `OAI.Erdos3.polynomialShearLogValue_lower`, `OAI.Erdos3.polynomialShearLogValue_mul`, `OAI.Erdos3.polynomialShearLogValue_smul`, `OAI.Erdos3.polynomialShearLog_apply`, `OAI.Erdos3.polynomialShearLog_end`, `OAI.Erdos3.polynomialShearLog_exp`, `OAI.Erdos3.polynomialShearMonomial`, `OAI.Erdos3.polynomialShearMonomial_X`, `OAI.Erdos3.polynomialShearMonomial_repr`, `OAI.Erdos3.polynomialShear_X_mass_of_coordinates`, `OAI.Erdos3.polynomialShear_factorial_exp_integral`, `OAI.Erdos3.polynomialShear_factorial_log_integral`, `OAI.Erdos3.polynomialShear_finrank_le`, `OAI.Erdos3.polynomialShear_pow_degree`, `OAI.Erdos3.polynomialShear_pow_mass`, `OAI.Erdos3.polynomialShear_scaled_pow`, `OAI.Erdos3.polynomialSymbolicShearDerivation`, `OAI.Erdos3.polynomialSymbolicShearDerivation_X_parameter`, `OAI.Erdos3.polynomialSymbolicShearDerivation_X_slot`, `OAI.Erdos3.polynomialSymbolicShearDerivation_total_degree`, `OAI.Erdos3.polynomialSymbolicShearDerivation_weighted_degree`, `OAI.Erdos3.polynomialSymbolicShearExp_total_degree`, `OAI.Erdos3.polynomialSymbolicShearExp_weighted_degree`, `OAI.Erdos3.polynomialSymbolicShearSlot`, `OAI.Erdos3.polynomialSymbolicShearSlot_lower`, `OAI.Erdos3.polynomialSymbolicShearTerm`, `OAI.Erdos3.polynomialSymbolicShearTerm_slot_degree`, `OAI.Erdos3.polynomialSymbolicShearTerm_total_degree`, `OAI.Erdos3.polynomialSymbolicShearTerm_weighted_degree`, `OAI.Erdos3.polynomialTranslate_comp_ring`, `OAI.Erdos3.polynomialTranslate_eval_ring`, `OAI.Erdos3.polynomialTranslate_map_ring`, `OAI.Erdos3.polynomialTranslate_zero_ring`, `OAI.Erdos3.potentialExponent`, `OAI.Erdos3.rationalMajorRight`, `OAI.Erdos3.real_fourierChar_add_integer`, `OAI.Erdos3.real_fourierChar_sub_star`, `OAI.Erdos3.real_grid_polynomial_residue_difference`, `OAI.Erdos3.residueAffinePolynomial`, `OAI.Erdos3.residueAffinePolynomial_eval`, `OAI.Erdos3.residueAffinePolynomial_totalDegree_le`, `OAI.Erdos3.specializeMajorParameters`, `OAI.Erdos3.specializeMajorParameters_eval`, `OAI.Erdos3.specializeMajorParameters_translatedSlice`, `OAI.Erdos3.specializeMajorParameters_zero_weightedSupportLE`, `OAI.Erdos3.translationPhaseArgument`, `OAI.Erdos3.translationPhaseArgument_fourier_integer`, `OAI.Erdos3.translationPhaseArgument_integer_character`, `OAI.Erdos3.translationPhaseArgument_left_increment`, `OAI.Erdos3.translationPhaseArgument_majorSymbol`, `OAI.Erdos3.translationPhaseArgument_mul`, `OAI.Erdos3.translationPhaseFunction`, `OAI.Erdos3.translationPhaseFunction_central`, `OAI.Erdos3.translationPhaseFunction_integerSubgroup`, `OAI.Erdos3.translationPhaseFunction_integer_lattice`, `OAI.Erdos3.translationQuotientPhase`, `OAI.Erdos3.translationQuotientPhase_mk`, `OAI.Erdos3.weightedPolynomialEndAlgebra`, `OAI.Erdos3.weightedPolynomialEndAlgebraRing`, `OAI.Erdos3.weightedPolynomialEndDrop`, `OAI.Erdos3.weightedPolynomialEndDrop_antitone`, `OAI.Erdos3.weightedPolynomialEndDrop_mul`, `OAI.Erdos3.weightedPolynomialEndDrop_one`, `OAI.Erdos3.weightedPolynomialEndDrop_terminal`, `OAI.Erdos3.weightedPolynomialEndFiltration`, `OAI.Erdos3.weightedPolynomialEndLayer`, `OAI.Erdos3.weightedPolynomialMul`, `OAI.Erdos3.weightedSupportLE_finrank_le`, `OAI.Erdos3.weightedSupportLE_moduleFinite`, `_private.Estimates.VectorAlgebraicMajorDecomposition.0.OAI.Erdos3.majorFunctionAdd`, `_private.Estimates.VectorAlgebraicMajorDecomposition.0.OAI.Erdos3.majorFunctionNeg`, `_private.Estimates.VectorAlgebraicMajorDecomposition.0.OAI.Erdos3.majorFunctionSub`, `_private.Polynomial.PolynomialSymbolicShearWeightedDegree.0.OAI.Erdos3.symbolic_rename_degree`, `_private.Polynomial.PolynomialSymbolicShearWeightedDegree.0.OAI.Erdos3.weighted_symbolic_rename_degree`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalBoostedAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem setAverageTranslate_sub (A : Finset (ZMod N)) (f g : ZMod N → ℝ) (x : ZMod N) :
    setAverageTranslate A (fun y => f y - g y) x =
      setAverageTranslate A f x - setAverageTranslate A g x := by
  simp only [setAverageTranslate, Finset.sum_sub_distrib, sub_div]

omit [NeZero N] in
theorem setAverageTranslate_rightTranslate (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x t : ZMod N) :
    setAverageTranslate A (fun y => f (y + t)) x = setAverageTranslate A f (x + t) := by
  unfold setAverageTranslate
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change f (x - a + t) = f (x + t - a)
  rw [show x - a + t = x + t - a by abel]

omit [NeZero N] in
theorem setAverageTranslate_abs_pow_le {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (x : ZMod N) (n : ℕ) :
    |setAverageTranslate A f x| ^ n ≤ (∑ a ∈ A, |f (x - a)| ^ n) / A.card := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  cases n with
  | zero => simp [hc.ne']
  | succ n =>
    have habs : |setAverageTranslate A f x| ≤ (∑ a ∈ A, |f (x - a)|) / A.card := by
      rw [setAverageTranslate, abs_div, abs_of_pos hc]
      exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
    have hj := pow_sum_div_card_le_sum_pow (s := A) (fun a _ => abs_nonneg (f (x - a))) n
    calc
      _ ≤ ((∑ a ∈ A, |f (x - a)|) / A.card) ^ (n + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) habs _
      _ = (∑ a ∈ A, |f (x - a)|) ^ (n + 1) / (A.card : ℝ) ^ n / A.card := by
        rw [div_pow, pow_succ (A.card : ℝ) n, div_mul_eq_div_div]
      _ ≤ _ := div_le_div_of_nonneg_right hj hc.le

theorem setAverageTranslate_abs_pow_le_total {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (x : ZMod N) (n : ℕ) :
    |setAverageTranslate A f x| ^ n ≤ (∑ y, |f y| ^ n) / A.card := by
  apply (setAverageTranslate_abs_pow_le hA f x n).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ y, |f (x - y)| ^ n := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ A) (fun _ _ _ => by positivity)
    _ = _ := Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)

theorem convolution_period_moment_bound {L : Finset (ZMod N)} (hL : L.Nonempty)
    (u : ZMod N → ℝ) (t x : ZMod N) (n : ℕ) {E : ℝ}
    (hperiod : ∑ y, |u (y + t) - u y| ^ n ≤ E) :
    |setAverageTranslate L u (x + t) - setAverageTranslate L u x| ^ n ≤ E / L.card := by
  have h := setAverageTranslate_abs_pow_le_total hL (fun y => u (y + t) - u y) x n
  rw [setAverageTranslate_sub, setAverageTranslate_rightTranslate] at h
  exact h.trans (div_le_div_of_nonneg_right hperiod (Nat.cast_nonneg _))

def realSetIndicator (M : Finset (ZMod N)) (x : ZMod N) : ℝ := if x ∈ M then 1 else 0

theorem sum_realSetIndicator_moment (M : Finset (ZMod N)) {n : ℕ} (hn : n ≠ 0) :
    (∑ x, |realSetIndicator M x| ^ n) = (M.card : ℝ) := by
  have hp (x : ZMod N) : |realSetIndicator M x| ^ n = if x ∈ M then 1 else 0 := by
    by_cases hx : x ∈ M <;> simp [realSetIndicator, hx, hn]
  simp only [hp]
  simp

theorem triple_period_moment_bound {L : Finset (ZMod N)} (hL : L.Nonempty)
    (A M : Finset (ZMod N)) (t x : ZMod N) {n : ℕ} (hn : n ≠ 0) {epsilon : ℝ}
    (hperiod : ∑ y,
      |setAverageTranslate A (realSetIndicator M) (y + t) -
        setAverageTranslate A (realSetIndicator M) y| ^ n ≤
          epsilon ^ n * ∑ y, |realSetIndicator M y| ^ n) :
    |setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) (x + t) -
      setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x| ^ n ≤
        epsilon ^ n * ((M.card : ℝ) / L.card) := by
  have h := convolution_period_moment_bound hL
    (setAverageTranslate A (realSetIndicator M)) t x n hperiod
  simpa only [sum_realSetIndicator_moment M hn, mul_div_assoc] using h

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

theorem half_card_le_filter_of_sum_le {ι : Type*} (S : Finset ι) (g : ι → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ a ∈ S, 0 ≤ g a)
    (htotal : ∑ a ∈ S, g a ≤ (1 / 2 : ℝ) * C * S.card) :
    (S.card : ℝ) / 2 ≤ (S.filter (fun a => g a ≤ C)).card := by
  classical
  by_cases hpos : 0 < C
  · have h := markov_card_good hpos hg htotal
    norm_num at h
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using h
  · have hzero : C = 0 := le_antisymm (not_lt.mp hpos) hC
    have hsum : ∑ a ∈ S, g a = 0 := by
      apply le_antisymm
      · simpa only [hzero, mul_zero, zero_mul] using htotal
      · exact Finset.sum_nonneg hg
    have hpoint := (Finset.sum_eq_zero_iff_of_nonneg hg).mp hsum
    have hfilter : S.filter (fun a => g a ≤ C) = S := by
      apply Finset.filter_eq_self.mpr
      intro a ha
      rw [hpoint a ha, hzero]
    rw [hfilter]
    have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    linarith

variable {N k m : ℕ} [NeZero N]

theorem half_samples_good_input_moment {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (hm : m ≠ 0) :
    (A.card : ℝ) ^ k / 2 ≤
      (goodSamples A f k m (samplingMomentCost m k * ∑ x, |f x| ^ (2 * m))).card := by
  let C := samplingMomentCost m k * ∑ x, |f x| ^ (2 * m)
  have hC : 0 ≤ C := mul_nonneg (samplingMomentCost_nonneg _ _)
    (Finset.sum_nonneg (fun _ _ => by positivity))
  have htotal : ∑ a ∈ A ^^ k, ∑ x, |sampleDeviation A f a x| ^ (2 * m) ≤
      (1 / 2 : ℝ) * C * (A ^^ k).card := by
    apply (global_sampleDeviation_input_moment (k := k) hA f hm).trans_eq
    simp only [C, samplingMomentCost, Fintype.card_piFinset_const, Nat.cast_pow]
    ring
  have h := half_card_le_filter_of_sum_le (A ^^ k)
    (fun a => ∑ x, |sampleDeviation A f a x| ^ (2 * m)) hC
    (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) htotal
  simpa only [goodSamples, C, Fintype.card_piFinset_const, Nat.cast_pow] using h

theorem goodSamples_relative_moment_bound {A : Finset (ZMod N)} {f : ZMod N → ℝ}
    (hm : 0 < m) (hk : 0 < k) {epsilon : ℝ}
    (hsize : 256 * (m : ℝ) ≤ epsilon ^ 2 * k)
    {a : Fin k → ZMod N} {t : ZMod N}
    (ha : a ∈ goodSamples A f k m (samplingMomentCost m k * ∑ x, |f x| ^ (2 * m)))
    (hat : (a - fun _ => t) ∈
      goodSamples A f k m (samplingMomentCost m k * ∑ x, |f x| ^ (2 * m))) :
    ∑ x, |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) ≤
      epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  have hraw := goodSamples_give_almost_period ha hat
  have hbudget := samplingMomentCost_error hm hsize
  have hS : (0 : ℝ) ≤ ∑ x, |f x| ^ (2 * m) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hupper := mul_le_mul_of_nonneg_right hbudget hS
  have hfinal : (k : ℝ) ^ (2 * m) *
      (∑ x, |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m)) ≤
        (k : ℝ) ^ (2 * m) * (epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
    apply hraw.trans
    simpa only [mul_assoc] using hupper
  exact le_of_mul_le_mul_left hfinal (pow_pos (by exact_mod_cast hk) _)

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

variable {N : ℕ}

noncomputable def convolutionMomentOrder (M L : Finset (ZMod N)) : ℕ :=
  ⌈1 + Real.log (max 1 ((M.card : ℝ) / L.card))⌉₊

theorem convolutionMomentOrder_pos (M L : Finset (ZMod N)) :
    0 < convolutionMomentOrder M L := by
  apply Nat.ceil_pos.mpr
  have h := Real.log_nonneg (le_max_left 1 ((M.card : ℝ) / L.card))
  linarith

theorem cardinal_ratio_le_exp_momentOrder (M L : Finset (ZMod N)) :
    (M.card : ℝ) / L.card ≤ Real.exp (2 * (convolutionMomentOrder M L : ℝ)) := by
  let R : ℝ := max 1 ((M.card : ℝ) / L.card)
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hceil : 1 + Real.log R ≤ (convolutionMomentOrder M L : ℝ) := Nat.le_ceil _
  have hm : (0 : ℝ) ≤ convolutionMomentOrder M L := Nat.cast_nonneg _
  calc
    _ ≤ R := le_max_right _ _
    _ = Real.exp (Real.log R) := (Real.exp_log hR).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem convolution_moment_to_pointwise (M L : Finset (ZMod N)) {delta z : ℝ}
    (hdelta : 0 < delta)
    (hz : |z| ^ (2 * convolutionMomentOrder M L) ≤
      (delta / Real.exp 1) ^ (2 * convolutionMomentOrder M L) * ((M.card : ℝ) / L.card)) :
    |z| ≤ delta := by
  let m := convolutionMomentOrder M L
  have hm : 0 < m := convolutionMomentOrder_pos M L
  have hexp : Real.exp (2 * (m : ℝ)) = Real.exp 1 ^ (2 * m) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 (2 * m)
  apply le_of_pow_le_pow_left₀ (show 2 * m ≠ 0 by omega) hdelta.le
  calc
    _ ≤ (delta / Real.exp 1) ^ (2 * m) * ((M.card : ℝ) / L.card) := hz
    _ ≤ (delta / Real.exp 1) ^ (2 * m) * Real.exp (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (cardinal_ratio_le_exp_momentOrder M L) (by positivity)
    _ = delta ^ (2 * m) := by
      rw [hexp, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Real.exp_ne_zero _))]

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

variable {N : ℕ}

theorem setAverageTranslate_approx_of_shifts {A : Finset (ZMod N)} (hA : A.Nonempty)
    (u : ZMod N → ℝ) {delta : ℝ}
    (hshift : ∀ t ∈ A, ∀ x, |u (x + t) - u x| ≤ delta) (x : ZMod N) :
    |setAverageTranslate A u x - u x| ≤ delta := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have heq : setAverageTranslate A u x - u x =
      (∑ t ∈ A, (u (x - t) - u x)) / A.card := by
    rw [setAverageTranslate, Finset.sum_sub_distrib, sub_div]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hpoint (t : ZMod N) (ht : t ∈ A) : |u (x - t) - u x| ≤ delta := by
    have h := hshift t ht (x - t)
    simpa only [sub_add_cancel, abs_sub_comm] using h
  rw [heq, abs_div, abs_of_pos hc]
  calc
    _ ≤ (∑ t ∈ A, |u (x - t) - u x|) / A.card :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
    _ ≤ (∑ _t ∈ A, delta) / A.card :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) hc.le
    _ = delta := by simp [hc.ne']

noncomputable def iteratedSetAverage (A : Finset (ZMod N)) (u : ZMod N → ℝ) :
    ℕ → ZMod N → ℝ
  | 0 => u
  | n + 1 => setAverageTranslate A (iteratedSetAverage A u n)

theorem iteratedSetAverage_uniform_error {A : Finset (ZMod N)} (hA : A.Nonempty)
    (u : ZMod N → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hstep : ∀ x, |setAverageTranslate A u x - u x| ≤ delta) (n : ℕ) :
    ∀ x, |iteratedSetAverage A u n x - u x| ≤ n * delta := by
  induction n with
  | zero => intro x; simp [iteratedSetAverage]
  | succ n ih =>
    intro x
    change |setAverageTranslate A (iteratedSetAverage A u n) x - u x| ≤ _
    have herror : |setAverageTranslate A (iteratedSetAverage A u n) x - setAverageTranslate A u x| ≤
        n * delta := by
      rw [← setAverageTranslate_sub]
      exact abs_setAverageTranslate_le hA (fun y => iteratedSetAverage A u n y - u y)
        (mul_nonneg (Nat.cast_nonneg _) hdelta) ih x
    calc
      _ = |(setAverageTranslate A (iteratedSetAverage A u n) x - setAverageTranslate A u x) +
          (setAverageTranslate A u x - u x)| := by congr 1; ring
      _ ≤ |setAverageTranslate A (iteratedSetAverage A u n) x - setAverageTranslate A u x| +
          |setAverageTranslate A u x - u x| := abs_add_le _ _
      _ ≤ n * delta + delta := add_le_add herror (hstep x)
      _ = _ := by push_cast; ring

theorem iteratedSetAverage_approx_of_shifts {A : Finset (ZMod N)} (hA : A.Nonempty)
    (u : ZMod N → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hshift : ∀ t ∈ A, ∀ x, |u (x + t) - u x| ≤ delta) (n : ℕ) (x : ZMod N) :
    |iteratedSetAverage A u n x - u x| ≤ n * delta :=
  iteratedSetAverage_uniform_error hA u hdelta (setAverageTranslate_approx_of_shifts hA u hshift) n x

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators Pointwise

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {N : ℕ} [NeZero N]

theorem exists_local_almostPeriods {A S : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (f : ZMod N → ℝ)
    {m : ℕ} (hm : 0 < m) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let k := crootSisaskSampleSize m epsilon
    ∃ T : Finset (ZMod N), T ⊆ S ∧ T.Nonempty ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      ∀ s ∈ T, ∀ t ∈ T,
        ∑ x, |setAverageTranslate A f (x + (t - s)) - setAverageTranslate A f x| ^ (2 * m) ≤
          epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  classical
  intro k
  let C := samplingMomentCost m k * ∑ x, |f x| ^ (2 * m)
  let L := goodSamples A f k m C
  have hhalf : (A.card : ℝ) ^ k / 2 ≤ L.card := half_samples_good_input_moment hA f hm.ne'
  have hLpos : (0 : ℝ) < L.card :=
    (div_pos (pow_pos (by exact_mod_cast hA.card_pos) _) (by norm_num)).trans_le hhalf
  have hL : L.Nonempty := Finset.card_pos.mp (by exact_mod_cast hLpos)
  have hLA : L ⊆ A ^^ k := Finset.filter_subset _ _
  obtain ⟨x, T, hTS, hT, hcount, hgood⟩ := exists_local_shift_fiber hA hS L hL hLA
  refine ⟨T, hTS, hT, ?_, ?_⟩
  · apply le_trans _ hcount
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)) (by positivity)
  · intro s hs t ht
    have hbase : (x - fun _ => s) ∈ goodSamples A f k m C := hgood s hs
    have hshift : ((x - fun _ => s) - fun _ => t - s) ∈ goodSamples A f k m C := by
      have heq : ((x - fun _ => s) - fun _ => t - s) = x - fun _ => t := by
        funext i
        simp only [Pi.sub_apply]
        abel
      rw [heq]
      exact hgood t ht
    exact goodSamples_relative_moment_bound hm (crootSisaskSampleSize_pos hm hepsilon)
      (crootSisaskSampleSize_bound m hepsilon) hbase hshift

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_local_triple_almostPeriods {A S L : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (M : Finset (ZMod N)) {delta : ℝ} (hdelta : 0 < delta) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m (delta / Real.exp 1)
    ∃ T : Finset (ZMod N), T ⊆ S ∧ T.Nonempty ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      ∀ s ∈ T, ∀ t ∈ T, ∀ x : ZMod N,
        |setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) (x + (t - s)) -
          setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x| ≤ delta := by
  intro m k
  obtain ⟨T, hTS, hT, hcount, hperiod⟩ := exists_local_almostPeriods hA hS (realSetIndicator M)
    (convolutionMomentOrder_pos M L) (div_pos hdelta (Real.exp_pos _))
  refine ⟨T, hTS, hT, hcount, ?_⟩
  intro s hs t ht x
  apply convolution_moment_to_pointwise M L hdelta
  exact triple_period_moment_bound hL A M (t - s) x
    (show 2 * m ≠ 0 by have := convolutionMomentOrder_pos M L; dsimp only [m]; omega)
    (hperiod s hs t ht)

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_local_boosted_triple_almostPeriods {A S L : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (M : Finset (ZMod N)) (q : ℕ) (hq : 0 < q) {delta : ℝ} (hdelta : 0 < delta) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m ((delta / q) / Real.exp 1)
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ (T X : Finset (ZMod N)) (z : ZMod N), T ⊆ S ∧ z ∈ T ∧
      X = T.map (Equiv.subRight z).toEmbedding ∧ 0 ∈ X ∧ X ⊆ S - S ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      ∀ x, |iteratedSetAverage X u q x - u x| ≤ delta := by
  intro m k u
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdeltaq : 0 < delta / (q : ℝ) := div_pos hdelta hqR
  obtain ⟨T, hTS, hT, hcount, hperiod⟩ := exists_local_triple_almostPeriods hA hS hL M hdeltaq
  obtain ⟨z, hz⟩ := hT
  let X := T.map (Equiv.subRight z).toEmbedding
  have hzero : (0 : ZMod N) ∈ X := by
    apply Finset.mem_map.mpr
    exact ⟨z, hz, sub_self z⟩
  have hXS : X ⊆ S - S := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ht
    exact Finset.sub_mem_sub (hTS ha) (hTS hz)
  refine ⟨T, X, z, hTS, hz, rfl, hzero, hXS, hcount, ?_⟩
  have hshift : ∀ t ∈ X, ∀ x, |u (x + t) - u x| ≤ delta / (q : ℝ) := by
    intro t ht x
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ht
    exact hperiod z hz a ha x
  intro x
  have h := iteratedSetAverage_approx_of_shifts (show X.Nonempty from ⟨0, hzero⟩)
    u hdeltaq.le hshift q x
  have hcancel : (q : ℝ) * (delta / q) = delta := by field_simp
  exact h.trans_eq hcancel

end Erdos3.CyclicCrootSisask

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SpectralLogBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

noncomputable def spectralIterations (epsilon p : ℝ) : ℕ :=
  ⌈(p + Real.log (16 / epsilon)) / Real.log 2⌉₊ + 1

noncomputable def spectralIterationFactor (epsilon : ℝ) : ℝ :=
  (1 + Real.log (16 / epsilon)) / Real.log 2 + 2

theorem spectralIterations_pos (epsilon p : ℝ) : 0 < spectralIterations epsilon p := by
  unfold spectralIterations
  omega

theorem spectralIterations_le {epsilon p : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p) :
    (spectralIterations epsilon p : ℝ) ≤ spectralIterationFactor epsilon * (p + 1) := by
  have hlog : 0 ≤ Real.log (16 / epsilon) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hepsilon]
    linarith
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (p + Real.log (16 / epsilon)) / Real.log 2 by positivity)
  have hfirst : (spectralIterations epsilon p : ℝ) ≤
      (p + Real.log (16 / epsilon)) / Real.log 2 + 2 := by
    unfold spectralIterations
    push_cast
    linarith
  apply hfirst.trans
  unfold spectralIterationFactor
  apply (le_of_sub_nonneg ?_)
  have hid : ((1 + Real.log (16 / epsilon)) / Real.log 2 + 2) * (p + 1) -
      ((p + Real.log (16 / epsilon)) / Real.log 2 + 2) =
      (1 + p * Real.log (16 / epsilon)) / Real.log 2 + 2 * p := by ring
  rw [hid]
  positivity

theorem half_pow_spectralIterations_mul_exp_le {epsilon p : ℝ} (hepsilon : 0 < epsilon) :
    (1 / 2 : ℝ) ^ spectralIterations epsilon p * Real.exp p ≤ epsilon / 16 := by
  let q := spectralIterations epsilon p
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : (p + Real.log (16 / epsilon)) / Real.log 2 ≤ (q : ℝ) := by
    apply (Nat.le_ceil _).trans
    dsimp [q, spectralIterations]
    exact_mod_cast Nat.le_succ _
  have hmul := (div_le_iff₀ htwo).mp hq
  have hpow : (1 / 2 : ℝ) ^ q = Real.exp (-((q : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [one_div, inv_pow]
  calc
    (1 / 2 : ℝ) ^ q * Real.exp p = Real.exp (-((q : ℝ) * Real.log 2) + p) := by
      rw [hpow, ← Real.exp_add]
    _ ≤ Real.exp (-Real.log (16 / epsilon)) := Real.exp_le_exp.mpr (by linarith)
    _ = epsilon / 16 := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 16 / epsilon)]
      field_simp

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UniformExternalNetScalarBudget
namespace OAI

section

namespace Erdos3

theorem exists_uniformExternalNetScalarBudget (netExponent localExponent : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p ε : ℝ, 0 ≤ p → 0 < ε → ε ≤ 1 →
      ∃ q : ℝ, 0 ≤ q ∧ p ≤ q ∧ Real.log (1 / ε) ≤ q ∧
        (p + Real.log (1 / (ε / 3)) + netExponent) ^ netExponent ≤ q ∧
        (q + localExponent) ^ localExponent ≤ (p + Real.log (1 / ε) + C) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C netExponent + 3) ^ netExponent +
      3 + Polynomial.C localExponent) ^ localExponent
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p ε hp hε hε1
  have hlog : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div hε).2 hε1)
  have hlogThree : Real.log (1 / (ε / 3)) = Real.log (1 / ε) + Real.log 3 := by
    rw [show (1 : ℝ) / (ε / 3) = (1 / ε) * 3 by field_simp]
    exact Real.log_mul (by positivity) (by norm_num)
  have hthree : Real.log (3 : ℝ) ≤ 3 := Real.log_le_self (by norm_num)
  have hthree0 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  let x := p + Real.log (1 / ε)
  have hx : 0 ≤ x := add_nonneg hp hlog
  let q := x + (x + netExponent + 3) ^ netExponent + 3
  have hpower : 0 ≤ (x + netExponent + 3) ^ netExponent := by positivity
  refine ⟨q, by dsimp [q]; positivity, ?_, ?_, ?_, ?_⟩
  · dsimp [q, x]
    linarith only [hlog, hpower]
  · dsimp [q, x]
    linarith only [hp, hpower]
  · have hbase0 : 0 ≤ p + Real.log (1 / (ε / 3)) + netExponent := by
      rw [hlogThree]
      positivity
    have hbase : p + Real.log (1 / (ε / 3)) + netExponent ≤
        x + netExponent + 3 := by
      rw [hlogThree]
      dsimp [x]
      linarith only [hthree]
    exact (pow_le_pow_left₀ hbase0 hbase netExponent).trans (by dsimp [q]; linarith)
  · simpa [P, q, x, Polynomial.eval₂_pow] using hbudget x hx

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth
namespace OAI

section

open Filter

namespace Erdos3

def amplificationGain (κ H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | j + 1 => κ * amplificationGain κ H₀ j ^ 2

def amplificationResource (p : ℝ) (D K : ℕ) : ℕ → ℝ
  | 0 => (2 + p) ^ D
  | j + 1 => (2 + amplificationResource p D K j) ^ K

end Erdos3

end

section

namespace Erdos3

noncomputable def levelCoefficient (K : ℝ) : ℝ := 1 / (4 * Real.log K)

noncomputable def gainExponent (K : ℝ) : ℝ := levelCoefficient K * Real.log 2

noncomputable def potentialExponent (K : ℝ) : ℝ := 1 - gainExponent K / 2

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantObservableMemberNets
namespace OAI

section

namespace Erdos3
open scoped Classical

theorem constantObservable_memberNets
    {Z Y : Type*} (box : Finset Z) (hbox : box.Nonempty)
    (F : Y → ℂ) {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : Z // x ∈ box},
        ∀ x ∈ box, ∃ i, ∀ y,
          ‖(fun (_ : Z) => F) x y - (fun (_ : Z) => F) (oc i).val y‖ ≤ η := by
  intro η hη hηone
  have hlog : 0 ≤ Real.log (1 / η) :=
    Real.log_nonneg ((le_div_iff₀ hη).mpr (by simpa using hηone))
  have hpower : 0 ≤ (p + Real.log (1 / η) + (e : ℝ)) ^ e :=
    pow_nonneg (add_nonneg (add_nonneg hp hlog) (Nat.cast_nonneg e)) e
  obtain ⟨z, hz⟩ := hbox
  refine ⟨1, (by simpa using Real.one_le_exp_iff.mpr hpower), (fun _ => ⟨z, hz⟩), ?_⟩
  intro x hx
  exact ⟨0, fun y => by simpa using hη.le⟩

theorem constantObservable_integerBox_memberNets
    {X Y : Type*} [Fintype X] (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (F : Y → ℂ) {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖(fun (_ : X → ℤ) => F) x y - (fun (_ : X → ℤ) => F) (oc i).val y‖ ≤ η := by
  have hzero : (0 : X → ℤ) ∈ integerBox N := by
    apply (mem_integerBox N 0).mpr
    intro x
    exact ⟨le_rfl, by change (0 : ℤ) < N x; exact_mod_cast hN x⟩
  exact constantObservable_memberNets (integerBox N) ⟨0, hzero⟩ F hp e

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorAlgebraicMajorDecomposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {R B : Type*} [CommRing R]

theorem polynomialTranslate_comp_ring (h k : B → R) (P : MvPolynomial B R) :
    polynomialTranslate h (polynomialTranslate k P) = polynomialTranslate (h + k) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, polynomialTranslate_X, map_add, polynomialTranslate_C, Pi.add_apply]
    rw [add_assoc]

@[simp] theorem polynomialTranslate_zero_ring (P : MvPolynomial B R) :
    polynomialTranslate (0 : B → R) P = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp]

@[ext] structure PolynomialTranslationGroupOver (R B : Type*) [CommRing R] where
  base : B → R
  polynomial : MvPolynomial B R

namespace PolynomialTranslationGroupOver

noncomputable instance : Mul (PolynomialTranslationGroupOver R B) where
  mul a b := ⟨a.base + b.base, polynomialTranslate (-b.base) a.polynomial + b.polynomial⟩

noncomputable instance : One (PolynomialTranslationGroupOver R B) where
  one := ⟨0, 0⟩

noncomputable instance : Inv (PolynomialTranslationGroupOver R B) where
  inv a := ⟨-a.base, -polynomialTranslate a.base a.polynomial⟩

@[simp] theorem base_mul (a b : PolynomialTranslationGroupOver R B) :
    (a * b).base = a.base + b.base := rfl

@[simp] theorem polynomial_mul (a b : PolynomialTranslationGroupOver R B) :
    (a * b).polynomial = polynomialTranslate (-b.base) a.polynomial + b.polynomial := rfl

@[simp] theorem base_one : (1 : PolynomialTranslationGroupOver R B).base = 0 := rfl
@[simp] theorem polynomial_one : (1 : PolynomialTranslationGroupOver R B).polynomial = 0 := rfl
@[simp] theorem base_inv (a : PolynomialTranslationGroupOver R B) : (a⁻¹).base = -a.base := rfl
@[simp] theorem polynomial_inv (a : PolynomialTranslationGroupOver R B) :
    (a⁻¹).polynomial = -polynomialTranslate a.base a.polynomial := rfl

noncomputable instance : Group (PolynomialTranslationGroupOver R B) :=
  Group.ofLeftAxioms
    (by
      intro a b c
      apply PolynomialTranslationGroupOver.ext
      · exact add_assoc _ _ _
      · simp only [polynomial_mul, base_mul, map_add, polynomialTranslate_comp_ring,
          neg_add_rev, add_assoc])
    (by intro a; apply PolynomialTranslationGroupOver.ext <;> simp)
    (by
      intro a
      apply PolynomialTranslationGroupOver.ext
      · simp
      · simp [polynomialTranslate_comp_ring])

end PolynomialTranslationGroupOver

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R T : Type*} [CommRing R] [CommRing T]

noncomputable def specializeMajorParameters (φ : R →+* T)
    (P : MvPolynomial (U ⊕ B) R) (u : U → T) : MvPolynomial B T :=
  eval₂Hom (C.comp φ) (Sum.elim (fun i => C (u i)) X) P

theorem specializeMajorParameters_eval (φ : R →+* T)
    (P : MvPolynomial (U ⊕ B) R) (u : U → T) (b : B → T) :
    eval b (specializeMajorParameters φ P u) = eval₂ φ (Sum.elim u b) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [specializeMajorParameters]
  | add p q hp hq => simpa only [specializeMajorParameters, map_add, eval₂_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    simp only [specializeMajorParameters, coe_eval₂Hom] at hp
    cases i <;> simp [specializeMajorParameters, hp]

theorem polynomialTranslate_eval_ring (h : B → R) (P : MvPolynomial B R) (b : B → R) :
    eval b (polynomialTranslate h P) = eval (fun i => b i + h i) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, polynomialTranslate_X, map_add, eval_X, eval_C]

noncomputable def normalizedMajorLeft (E : MvPolynomial (U ⊕ B) ℝ)
    (e : B → MvPolynomial U ℝ) (H u : U → ℝ) : PolynomialTranslationGroupOver ℝ B :=
  ⟨fun j => eval (fun i => u i / H i) (e j),
    specializeMajorParameters (RingHom.id ℝ) E (fun i => u i / H i)⟩

noncomputable def rationalMajorRight (Q : MvPolynomial (U ⊕ B) ℚ)
    (a : B → MvPolynomial U ℚ) (u : U → ℝ) : PolynomialTranslationGroupOver ℝ B :=
  ⟨fun j => eval₂ (algebraMap ℚ ℝ) u (a j),
    specializeMajorParameters (algebraMap ℚ ℝ) Q u⟩

noncomputable def algebraicMajorSymbol (D : MvPolynomial (U ⊕ B) ℝ)
    (D₀ : MvPolynomial B ℝ) (A : B → MvPolynomial U ℝ) (u : U → ℝ) :
    PolynomialTranslationGroupOver ℝ B :=
  ⟨fun j => eval u (A j), specializeMajorParameters (RingHom.id ℝ) D u -
    polynomialTranslate (fun j => -eval u (A j)) D₀⟩

theorem algebraic_major_normalized_slow_mass
    (D₀ : MvPolynomial B ℝ) (E : MvPolynomial (U ⊕ B) ℝ)
    (V : MvPolynomial B ℚ) (e : B → MvPolynomial U ℝ)
    {M : ℝ} (hM : 0 ≤ M) (he : ∀ j, realPolynomialMass (e j) ≤ M) {d : ℕ}
    (hE : E.totalDegree ≤ d) (hV : (map (algebraMap ℚ ℝ) V).totalDegree ≤ d) :
    realPolynomialMass (majorSlowPolynomial D₀ E (map (algebraMap ℚ ℝ) V) e) ≤
      realPolynomialMass D₀ +
        (realPolynomialMass E + realPolynomialMass (map (algebraMap ℚ ℝ) V)) * (1 + M) ^ d :=
  majorSlowPolynomial_mass_le D₀ E (map (algebraMap ℚ ℝ) V) e hM he hE hV

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem majorFunctionAdd {B R : Type*} [Add R] (f g : B → R) :
    f + g = fun i => f i + g i := rfl

theorem majorFunctionSub {B R : Type*} [Sub R] (f g : B → R) :
    f - g = fun i => f i - g i := rfl

theorem majorFunctionNeg {B R : Type*} [Neg R] (f : B → R) :
    -f = fun i => -f i := rfl

namespace PolynomialTranslationGroupOver

theorem algebraic_major_eval_on_subspace
    {B R : Type*} [CommRing R] (K : Submodule R (B → R))
    (D D₀ V : MvPolynomial B R) (A : B → R)
    (left middle right : PolynomialTranslationGroupOver R B)
    (hfactor : (⟨A, D - polynomialTranslate (-A) D₀⟩ : PolynomialTranslationGroupOver R B) =
      left * middle * right)
    (hpotential : ∀ z ∈ K, eval z middle.polynomial = eval z V - eval (z - middle.base) V)
    (hright : right.base ∈ K) (b : B → R) (hb : b ∈ K) :
    eval b D = eval (b - A) D₀ + eval (b - A + left.base) left.polynomial -
      eval (b - A + left.base) V + eval b right.polynomial + eval (b - right.base) V := by
  have hbase : A = left.base + middle.base + right.base := congrArg base hfactor
  have hpoly := congrArg (fun g : PolynomialTranslationGroupOver R B => eval b g.polynomial) hfactor
  change eval b (D - polynomialTranslate (-A) D₀) =
    eval b (polynomialTranslate (-right.base)
      (polynomialTranslate (-middle.base) left.polynomial + middle.polynomial) +
        right.polynomial) at hpoly
  simp only [map_sub, map_add, polynomialTranslate_eval_ring] at hpoly
  have hpot := hpotential (b - right.base) (K.sub_mem hb hright)
  have hx' : b - right.base - middle.base = b - A + left.base := by rw [hbase]; abel
  rw [hx'] at hpot
  have hpoly' : eval b D - eval (b - A) D₀ =
      eval (b - right.base - middle.base) left.polynomial +
        eval (b - right.base) middle.polynomial + eval b right.polynomial := by
    simpa only [majorFunctionSub, majorFunctionAdd, majorFunctionNeg,
      sub_eq_add_neg, Pi.add_apply, Pi.neg_apply] using hpoly
  rw [hx', hpot] at hpoly'
  linear_combination hpoly'

end PolynomialTranslationGroupOver

theorem algebraic_major_normalized_identity_on_subspace
    {U B : Type*} (K : Submodule ℝ (B → ℝ))
    (D : MvPolynomial (U ⊕ B) ℝ) (D₀ : MvPolynomial B ℝ)
    (A : B → MvPolynomial U ℝ) (E : MvPolynomial (U ⊕ B) ℝ)
    (e : B → MvPolynomial U ℝ) (Q : MvPolynomial (U ⊕ B) ℚ)
    (a : B → MvPolynomial U ℚ) (V : MvPolynomial B ℚ) (H : U → ℝ)
    (middle : (U → ℝ) → PolynomialTranslationGroupOver ℝ B)
    (hfactor : ∀ u, algebraicMajorSymbol D D₀ A u =
      normalizedMajorLeft E e H u * middle u * rationalMajorRight Q a u)
    (hpotential : ∀ u, ∀ z ∈ K,
      eval z (middle u).polynomial = eval₂ (algebraMap ℚ ℝ) z V -
        eval₂ (algebraMap ℚ ℝ) (z - (middle u).base) V)
    (hright : ∀ u, (fun j => eval₂ (algebraMap ℚ ℝ) u (a j)) ∈ K)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) D =
      eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j)))
        (majorSlowPolynomial D₀ E (map (algebraMap ℚ ℝ) V) e) +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (majorRationalPolynomial Q V a) := by
  have h := PolynomialTranslationGroupOver.algebraic_major_eval_on_subspace K
    (specializeMajorParameters (RingHom.id ℝ) D u) D₀ (map (algebraMap ℚ ℝ) V)
    (fun j => eval u (A j)) (normalizedMajorLeft E e H u) (middle u)
    (rationalMajorRight Q a u) (hfactor u)
    (by simpa only [eval_map] using hpotential u) (hright u) b hb
  rw [majorSlowPolynomial_eval, majorRationalPolynomial_eval₂]
  simp only [normalizedMajorLeft, rationalMajorRight, specializeMajorParameters_eval,
    eval₂_id, eval_map] at h ⊢
  simpa only [majorFunctionSub, majorFunctionAdd, Pi.sub_apply, Pi.add_apply, add_assoc] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem specializeMajorParameters_translatedSlice {U B : Type*}
    (P0 : MvPolynomial B ℝ) (x : B → MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ)
      (eval₂Hom C (fun j => X (Sum.inr j) - rename Sum.inl (x j)) P0) u =
        polynomialTranslate (fun j => -eval u (x j)) P0 := by
  apply MvPolynomial.funext
  intro b
  rw [specializeMajorParameters_eval, polynomialTranslate_eval_ring]
  change eval₂ (RingHom.id ℝ) (Sum.elim u b)
    (eval₂ C (fun j => X (Sum.inr j) - rename Sum.inl (x j)) P0) = _
  rw [← eval₂_assoc]
  simp only [eval₂_id]
  apply congrArg (fun f : B → ℝ => eval f P0)
  funext j
  rw [map_sub, eval_X, eval_rename]
  rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem specializeMajorParameters_zero_weightedSupportLE (w : B → ℕ)
    {v : U → ℕ} {d : ℕ} {P : MvPolynomial (U ⊕ B) R}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) d) :
    specializeMajorParameters (RingHom.id R) P (fun _ => 0) ∈
      weightedSupportLE w d := by
  change aeval (Sum.elim (fun _ : U => C (0 : R)) X) P ∈ weightedSupportLE w d
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i
  cases i with
  | inl i => exact weightedSupportLE_C w (v i) 0
  | inr i => exact weightedSupportLE_X w i

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical

variable {X B J V : Type*} [Fintype J]
  [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationActionCompatibility
namespace OAI

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

noncomputable def integerCoefficientPolynomials (σ : Type*) : Subalgebra ℤ (MvPolynomial σ ℚ) :=
  (MvPolynomial.mapAlgHom (Int.castRingHom ℚ).toIntAlgHom).range

theorem mem_integerCoefficientPolynomials (P : MvPolynomial σ ℚ) :
    P ∈ integerCoefficientPolynomials σ ↔ ∃ Q : MvPolynomial σ ℤ,
      MvPolynomial.map (Int.castRingHom ℚ) Q = P := Iff.rfl

theorem mem_integerCoefficientPolynomials_iff (P : MvPolynomial σ ℚ) :
    P ∈ integerCoefficientPolynomials σ ↔ ∀ a, ∃ z : ℤ, P.coeff a = (z : ℚ) := by
  change P ∈ (MvPolynomial.mapAlgHom (Int.castRingHom ℚ).toIntAlgHom).range.toSubmodule ↔ _
  rw [MvPolynomial.range_mapAlgHom, MvPolynomial.mem_coeffsIn]
  constructor
  · intro h a
    obtain ⟨z, hz⟩ := h a
    exact ⟨z, hz.symm⟩
  · intro h a
    obtain ⟨z, hz⟩ := h a
    exact ⟨z, hz.symm⟩

theorem integerCoefficientPolynomials_X (i : σ) :
    (X i : MvPolynomial σ ℚ) ∈ integerCoefficientPolynomials σ :=
  ⟨X i, MvPolynomial.map_X _ _⟩

theorem integerCoefficientPolynomials_C (z : ℤ) :
    (C (z : ℚ) : MvPolynomial σ ℚ) ∈ integerCoefficientPolynomials σ :=
  ⟨C z, MvPolynomial.map_C _ _⟩

theorem integerCoefficientPolynomials_rat_smul {c : ℚ} (hc : ∃ z : ℤ, c = (z : ℚ))
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    c • P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨z, rfl⟩ := hc
  apply (mem_integerCoefficientPolynomials_iff _).mpr
  intro a
  obtain ⟨v, hv⟩ := (mem_integerCoefficientPolynomials_iff P).mp hP a
  refine ⟨z * v, ?_⟩
  simp [hv]

theorem integerPolynomialHom_preserves
    (F : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ)
    (hF : ∀ i, F (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    F P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  clear hP
  induction Q using MvPolynomial.induction_on with
  | C z =>
    rw [MvPolynomial.map_C]
    change F (C (z : ℚ)) ∈ integerCoefficientPolynomials σ
    rw [show F (C (z : ℚ)) = C (z : ℚ) from F.commutes _]
    exact integerCoefficientPolynomials_C z
  | add P Q hP hQ =>
    simpa only [map_add] using (integerCoefficientPolynomials σ).add_mem hP hQ
  | mul_X P i hP =>
    simpa only [map_mul, MvPolynomial.map_X] using
      (integerCoefficientPolynomials σ).mul_mem hP (hF i)

theorem integerPolynomialDerivation_preserves
    (D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ))
    (hD : ∀ i, D (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    D P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  clear hP
  induction Q using MvPolynomial.induction_on with
  | C z =>
    simp only [MvPolynomial.map_C, MvPolynomial.derivation_C]
    exact (integerCoefficientPolynomials σ).zero_mem
  | add P Q hP hQ =>
    simpa only [map_add] using (integerCoefficientPolynomials σ).add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul, MvPolynomial.map_X, D.leibniz, smul_eq_mul, smul_eq_mul]
    exact (integerCoefficientPolynomials σ).add_mem
      ((integerCoefficientPolynomials σ).mul_mem ⟨P, rfl⟩ (hD i))
      ((integerCoefficientPolynomials σ).mul_mem (integerCoefficientPolynomials_X i) hP)

theorem integerPolynomialDerivation_pow
    (D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ))
    (hD : ∀ i, D (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) (k : ℕ) :
    (D.toLinearMap ^ k) P ∈ integerCoefficientPolynomials σ := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact integerPolynomialDerivation_preserves D hD ih

end Erdos3

namespace Erdos3.PolynomialTranslationGroupOver

open _root_.MvPolynomial
variable {R σ : Type*} [CommRing R]

noncomputable def actionHom (g : PolynomialTranslationGroupOver R σ) :
    MvPolynomial (σ ⊕ Unit) R →ₐ[R] MvPolynomial (σ ⊕ Unit) R :=
  aeval (Sum.elim (fun i => X (Sum.inl i) + C (g.base i))
    (fun u => X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial)))

@[simp] theorem actionHom_X_inl (g : PolynomialTranslationGroupOver R σ) (i : σ) :
    actionHom g (X (Sum.inl i)) = X (Sum.inl i) + C (g.base i) := by simp [actionHom]

@[simp] theorem actionHom_X_inr (g : PolynomialTranslationGroupOver R σ) (u : Unit) :
    actionHom g (X (Sum.inr u)) =
      X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial) := by simp [actionHom]

@[simp] theorem actionHom_C (g : PolynomialTranslationGroupOver R σ) (r : R) :
    actionHom g (C r) = C r := by simp [actionHom]

theorem actionHom_rename (g : PolynomialTranslationGroupOver R σ) (P : MvPolynomial σ R) :
    actionHom g (rename Sum.inl P) = rename Sum.inl (polynomialTranslate g.base P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => simp only [map_mul,rename_X,actionHom_X_inl,hP,polynomialTranslate_X,
      map_add,rename_C]

@[simp] theorem actionHom_one (P : MvPolynomial (σ ⊕ Unit) R) : actionHom 1 P = P := by
  have hh : actionHom (1 : PolynomialTranslationGroupOver R σ) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp
  exact DFunLike.congr_fun hh P

theorem actionHom_mul (g h : PolynomialTranslationGroupOver R σ)
    (P : MvPolynomial (σ ⊕ Unit) R) :
    actionHom (g*h) P = actionHom g (actionHom h P) := by
  have hh : actionHom (g*h) = (actionHom g).comp (actionHom h) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => simp [Pi.add_apply, add_assoc]
    | inr u =>
      simp only [actionHom_X_inr,base_mul,polynomial_mul,map_add,polynomialTranslate_comp_ring,
        AlgHom.comp_apply,actionHom_rename]
      rw [show g.base + h.base + -h.base = g.base by abel]
      abel
  exact DFunLike.congr_fun hh P

noncomputable def action (g : PolynomialTranslationGroupOver R σ) :
    MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R :=
  { actionHom g with
    invFun := actionHom g⁻¹
    left_inv := fun P => by
      change actionHom g⁻¹ (actionHom g P) = P
      rw [← actionHom_mul, inv_mul_cancel, actionHom_one]
    right_inv := fun P => by
      change actionHom g (actionHom g⁻¹ P) = P
      rw [← actionHom_mul, mul_inv_cancel, actionHom_one] }

noncomputable def actionMonoidHom : PolynomialTranslationGroupOver R σ →*
    (MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R) where
  toFun := action
  map_one' := by apply AlgEquiv.ext; intro P; exact actionHom_one P
  map_mul' g h := by apply AlgEquiv.ext; intro P; exact actionHom_mul g h P

theorem actionMonoidHom_injective : Function.Injective (actionMonoidHom (R := R) (σ := σ)) := by
  intro g h heq
  have hb : g.base = h.base := by
    funext i
    have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R]
      MvPolynomial (σ ⊕ Unit) R => f (X (Sum.inl i))) heq
    change actionHom g (X (Sum.inl i)) = actionHom h (X (Sum.inl i)) at hh
    rw [actionHom_X_inl,actionHom_X_inl] at hh
    exact MvPolynomial.C_injective (σ ⊕ Unit) R (add_left_cancel hh)
  apply PolynomialTranslationGroupOver.ext hb
  have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R]
    MvPolynomial (σ ⊕ Unit) R => f (X (Sum.inr ()))) heq
  change actionHom g (X (Sum.inr ())) = actionHom h (X (Sum.inr ())) at hh
  rw [actionHom_X_inr,actionHom_X_inr] at hh
  have hp := MvPolynomial.rename_injective Sum.inl Sum.inl_injective (add_left_cancel hh)
  have hp' := congrArg (polynomialTranslate (-g.base)) hp
  simpa only [hb, polynomialTranslate_comp_ring, neg_add_cancel, polynomialTranslate_zero_ring] using hp'

end Erdos3.PolynomialTranslationGroupOver

namespace Erdos3

open _root_.MvPolynomial

variable {B R S : Type*} [CommRing R] [CommRing S]

theorem polynomialTranslate_map_ring (φ : R →+* S) (h : B → R)
    (P : MvPolynomial B R) :
    MvPolynomial.map φ (polynomialTranslate h P) =
      polynomialTranslate (fun i => φ (h i)) (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, polynomialTranslate_X, map_add, map_X, map_C]

namespace PolynomialTranslationGroupOver

noncomputable def map (φ : R →+* S) :
    PolynomialTranslationGroupOver R B →* PolynomialTranslationGroupOver S B where
  toFun g := ⟨fun i => φ (g.base i), MvPolynomial.map φ g.polynomial⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply PolynomialTranslationGroupOver.ext
    · ext i; simp
    · simp only [polynomial_mul, map_add, polynomialTranslate_map_ring]
      congr 1
      congr 1
      exact congrArg polynomialTranslate (funext (fun i => map_neg φ (h.base i)))

@[simp] theorem map_base (φ : R →+* S) (g : PolynomialTranslationGroupOver R B) (i : B) :
    (PolynomialTranslationGroupOver.map φ g).base i = φ (g.base i) := rfl

@[simp] theorem map_polynomial (φ : R →+* S) (g : PolynomialTranslationGroupOver R B) :
    (PolynomialTranslationGroupOver.map φ g).polynomial = MvPolynomial.map φ g.polynomial := rfl

end PolynomialTranslationGroupOver

end Erdos3

namespace Erdos3.PolynomialTranslationGroupOver

open _root_.MvPolynomial
variable {σ R : Type*} [CommRing R]

noncomputable def actionElement (x : σ → R) (Q : MvPolynomial σ R) :
    PolynomialTranslationGroupOver R σ := ⟨x, polynomialTranslate (-x) Q⟩

@[simp] theorem actionElement_X_inl (x : σ → R) (Q : MvPolynomial σ R) (i : σ) :
    actionMonoidHom (actionElement x Q) (X (Sum.inl i)) = X (Sum.inl i) + C (x i) :=
  actionHom_X_inl _ i

@[simp] theorem actionElement_X_inr (x : σ → R) (Q : MvPolynomial σ R) (u : Unit) :
    actionMonoidHom (actionElement x Q) (X (Sum.inr u)) = X (Sum.inr u) + rename Sum.inl Q := by
  change actionHom (actionElement x Q) (X (Sum.inr u)) = _
  rw [actionHom_X_inr]
  change X (Sum.inr u) + rename Sum.inl (polynomialTranslate x (polynomialTranslate (-x) Q)) = _
  rw [polynomialTranslate_comp_ring, add_neg_cancel, polynomialTranslate_zero_ring]

theorem action_eq_of_shape
    (f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R)
    (x : σ → R) (Q : MvPolynomial σ R)
    (hbase : ∀ i, f (X (Sum.inl i)) = X (Sum.inl i) + C (x i))
    (hextra : f (X (Sum.inr ())) = X (Sum.inr ()) + rename Sum.inl Q) :
    actionMonoidHom (actionElement x Q) = f := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i => exact (actionElement_X_inl x Q i).trans (hbase i).symm
  | inr u => cases u; exact (actionElement_X_inr x Q ()).trans hextra.symm

theorem existsUnique_action_of_shape
    (f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R)
    (x : σ → R) (Q : MvPolynomial σ R)
    (hbase : ∀ i, f (X (Sum.inl i)) = X (Sum.inl i) + C (x i))
    (hextra : f (X (Sum.inr ())) = X (Sum.inr ()) + rename Sum.inl Q) :
    ∃! g : PolynomialTranslationGroupOver R σ, actionMonoidHom g = f := by
  refine ⟨actionElement x Q, action_eq_of_shape f x Q hbase hextra, ?_⟩
  intro g hg
  exact actionMonoidHom_injective (hg.trans (action_eq_of_shape f x Q hbase hextra).symm)

end Erdos3.PolynomialTranslationGroupOver

namespace Erdos3

open _root_.MvPolynomial
variable {σ R : Type*} [CommRing R]

namespace PolynomialTranslationGroupOver

theorem action_inverse_X_inl_eval (g : PolynomialTranslationGroupOver R σ)
    (β : σ → R) (y : R) (i : σ) :
    eval (Sum.elim β (fun _ : Unit => y))
      ((actionMonoidHom g).symm (X (Sum.inl i))) = β i - g.base i := by
  have he : (actionMonoidHom g).symm = actionMonoidHom g⁻¹ := (map_inv actionMonoidHom g).symm
  rw [he]
  change eval _ (actionHom g⁻¹ (X (Sum.inl i))) = _
  rw [actionHom_X_inl]
  simp [sub_eq_add_neg]

theorem action_inverse_X_inr_eval (g : PolynomialTranslationGroupOver R σ)
    (β : σ → R) (y : R) :
    eval (Sum.elim β (fun _ : Unit => y))
      ((actionMonoidHom g).symm (X (Sum.inr ()))) = y - eval β g.polynomial := by
  have he : (actionMonoidHom g).symm = actionMonoidHom g⁻¹ := (map_inv actionMonoidHom g).symm
  rw [he]
  change eval _ (actionHom g⁻¹ (X (Sum.inr ()))) = _
  rw [actionHom_X_inr]
  simp only [base_inv,polynomial_inv,map_neg,polynomialTranslate_comp_ring,
    neg_add_cancel,polynomialTranslate_zero_ring]
  simp [MvPolynomial.eval_rename,sub_eq_add_neg]

end PolynomialTranslationGroupOver
end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem integerCoefficientPolynomials_C_iff (c : ℚ) :
    (C c : MvPolynomial σ ℚ) ∈ integerCoefficientPolynomials σ ↔
      ∃ z : ℤ, c = (z : ℚ) := by
  constructor
  · intro hc
    simpa using
      (mem_integerCoefficientPolynomials_iff (C c)).mp hc 0
  · rintro ⟨z, rfl⟩
    exact integerCoefficientPolynomials_C z

theorem integerCoefficientPolynomials_rename (f : σ → τ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    rename f P ∈ integerCoefficientPolynomials τ := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  exact ⟨rename f Q, MvPolynomial.map_rename _ _ _⟩

theorem integerCoefficientPolynomials_rename_iff (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ ℚ) :
    rename f P ∈ integerCoefficientPolynomials τ ↔
      P ∈ integerCoefficientPolynomials σ := by
  constructor
  · intro hP
    apply (mem_integerCoefficientPolynomials_iff P).mpr
    intro a
    simpa only [MvPolynomial.coeff_rename_mapDomain f hf] using
      (mem_integerCoefficientPolynomials_iff (rename f P)).mp hP (a.mapDomain f)
  · exact integerCoefficientPolynomials_rename f

theorem integerCoefficientPolynomials_translate (b : σ → ℚ)
    (hb : ∀ i, ∃ z : ℤ, b i = (z : ℚ))
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    polynomialTranslate b P ∈ integerCoefficientPolynomials σ := by
  apply integerPolynomialHom_preserves (polynomialTranslate b) _ hP
  intro i
  rw [polynomialTranslate_X]
  exact (integerCoefficientPolynomials σ).add_mem
    (integerCoefficientPolynomials_X i)
    ((integerCoefficientPolynomials_C_iff (b i)).mpr (hb i))

theorem integerCoefficientPolynomials_translate_iff (b : σ → ℚ)
    (hb : ∀ i, ∃ z : ℤ, b i = (z : ℚ)) (P : MvPolynomial σ ℚ) :
    polynomialTranslate b P ∈ integerCoefficientPolynomials σ ↔
      P ∈ integerCoefficientPolynomials σ := by
  constructor
  · intro hP
    have hneg : ∀ i, ∃ z : ℤ, (-b) i = (z : ℚ) := by
      intro i
      obtain ⟨z, hz⟩ := hb i
      exact ⟨-z, by simp [hz]⟩
    have h := integerCoefficientPolynomials_translate (-b) hneg hP
    simpa only [polynomialTranslate_comp_ring, neg_add_cancel,
      polynomialTranslate_zero_ring] using h
  · exact integerCoefficientPolynomials_translate b hb

end Erdos3

namespace Erdos3.PolynomialTranslationGroupOver

open _root_.MvPolynomial
variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem map_actionHom (φ : R →+* S) (g : PolynomialTranslationGroupOver R σ)
    (P : MvPolynomial (σ ⊕ Unit) R) :
    MvPolynomial.map φ (actionHom g P) =
      actionHom (PolynomialTranslationGroupOver.map φ g) (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP =>
      simp only [map_mul,hP,MvPolynomial.map_X]
      congr 1
      cases i with
      | inl i => simp
      | inr u =>
          simp only [actionHom_X_inr,map_add,map_X,MvPolynomial.map_rename,
            polynomialTranslate_map_ring,map_polynomial]
          rfl

noncomputable def rationalEquiv : PolynomialTranslationGroup σ ≃* PolynomialTranslationGroupOver ℚ σ where
  toFun g := ⟨g.base,g.polynomial⟩
  invFun g := ⟨g.base,g.polynomial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem rationalEquiv_action (g : PolynomialTranslationGroup σ) :
    actionMonoidHom (rationalEquiv g) = PolynomialTranslationGroup.actionMonoidHom g := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> rfl

end Erdos3.PolynomialTranslationGroupOver

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerWeightedLoweringGroup
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem integerWeightedLowering_preimage (e : WeightedLoweringAut w ℚ)
    (he : ∀ i, e.val (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ integerCoefficientPolynomials σ)
    (hdegree : P ∈ weightedSupportLE w n) :
    ∃ Q, Q ∈ integerCoefficientPolynomials σ ∧ Q ∈ weightedSupportLE w n ∧ e.val Q = P := by
  induction n generalizing P with
  | zero =>
    refine ⟨P, hP, hdegree, ?_⟩
    exact sub_eq_zero.mp (weightedSupportLT_zero_eq (e.difference_lower hdegree))
  | succ n ih =>
    have hI : e.val P - P ∈ integerCoefficientPolynomials σ :=
      (integerCoefficientPolynomials σ).sub_mem (integerPolynomialHom_preserves e.val.toAlgHom he hP) hP
    have hD : e.val P - P ∈ weightedSupportLE w n :=
      weightedSupportLT_succ_le (e.difference_lower hdegree)
    obtain ⟨Q, hQI, hQD, hQ⟩ := ih hI hD
    refine ⟨P - Q, (integerCoefficientPolynomials σ).sub_mem hP hQI,
      (weightedSupportLE w (n + 1)).sub_mem hdegree (weightedSupportLE_mono (Nat.le_succ n) hQD), ?_⟩
    rw [map_sub, hQ]
    abel

theorem integerWeightedLowering_inverse_preserves (e : WeightedLoweringAut w ℚ)
    (he : ∀ i, e.val (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    e.val.symm P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨Q, hQI, _, hQ⟩ := integerWeightedLowering_preimage e he hP
    ((mem_weightedSupportLE_iff w _ P).mpr le_rfl)
  have hEQ : e.val.symm P = Q := by
    apply e.val.injective
    rw [e.val.apply_symm_apply, hQ]
  rw [hEQ]
  exact hQI

noncomputable def integerWeightedLoweringSubgroup (w : σ → ℕ) : Subgroup (WeightedLoweringAut w ℚ) where
  carrier := {e | ∀ i, e.val (X i) ∈ integerCoefficientPolynomials σ}
  one_mem' := fun i => integerCoefficientPolynomials_X i
  mul_mem' := by
    intro e f he hf i
    exact integerPolynomialHom_preserves e.val.toAlgHom he (hf i)
  inv_mem' := by
    intro e he i
    exact integerWeightedLowering_inverse_preserves e he (integerCoefficientPolynomials_X i)

theorem integerWeightedLowering_preserves (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    e.val P ∈ integerCoefficientPolynomials σ :=
  integerPolynomialHom_preserves e.val.toAlgHom he hP

theorem integerWeightedLowering_difference_pow (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) (k : ℕ) :
    (polynomialHomDifference e.val.toAlgHom ^ k) P ∈ integerCoefficientPolynomials σ := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (integerCoefficientPolynomials σ).sub_mem (integerWeightedLowering_preserves e he ih) ih

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

theorem weightedSupportLE_moduleFinite [Finite σ] (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (n : ℕ) : Module.Finite R (weightedSupportLE (R := R) w n) := by
  let : Fintype {a : σ →₀ ℕ | Finsupp.weight w a ≤ n} :=
    (Finsupp.finite_of_nat_weight_le w (fun i => (hw i).ne') n).fintype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport R
    {a : σ →₀ ℕ | Finsupp.weight w a ≤ n})

theorem exponentSum_le_positive_weight (w : σ → ℕ) (hw : ∀ i, 0 < w i) (a : σ →₀ ℕ) :
    a.sum (fun _ n => n) ≤ Finsupp.weight w a := by
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right (a i) (hw i))

theorem weightedSupportLE_finrank_le {K : Type*} [Field K] [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ) :
    finrank K (weightedSupportLE (R := K) w n) ≤ (Fintype.card σ + 1) ^ n := by
  classical
  let hs := Finsupp.finite_of_nat_weight_le w (fun i => (hw i).ne') n
  let : Fintype {a : σ →₀ ℕ | Finsupp.weight w a ≤ n} := hs.fintype
  have hcard := boundedExponentSet_card_le hs.toFinset n (fun a ha =>
    (exponentSum_le_positive_weight w hw a).trans (hs.mem_toFinset.mp ha))
  change finrank K (MvPolynomial.restrictSupport K
    {a : σ →₀ ℕ | Finsupp.weight w a ≤ n}) ≤ _
  rw [finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K
    {a : σ →₀ ℕ | Finsupp.weight w a ≤ n})]
  simpa only [Set.Finite.card_toFinset] using hcard

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {B U : Type*}

noncomputable def translationPhaseArgument (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) : ℝ :=
  eval β g.polynomial + eval (β - g.base) D₀

theorem translationPhaseArgument_mul (D₀ : MvPolynomial B ℝ)
    (g γ : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) :
    translationPhaseArgument D₀ (g * γ) (β + γ.base) =
      translationPhaseArgument D₀ g β + eval (β + γ.base) γ.polynomial := by
  simp only [translationPhaseArgument, PolynomialTranslationGroupOver.polynomial_mul,
    PolynomialTranslationGroupOver.base_mul, map_add, polynomialTranslate_eval_ring]
  have h₁ : (fun i => (β + γ.base) i + (-γ.base) i) = β := by ext i; simp
  have h₂ : β + γ.base - (g.base + γ.base) = β - g.base := by abel
  rw [h₁, h₂]
  ring

theorem eval_integer_polynomial_real (Q : MvPolynomial B ℤ) (β : B → ℤ) :
    eval (fun i => (β i : ℝ)) (MvPolynomial.map (Int.castRingHom ℝ) Q) =
      (eval β Q : ℝ) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, Int.cast_add]
  | mul_X p i hp => simp only [map_mul, map_X, eval_X, hp, Int.cast_mul]

theorem translationPhaseArgument_integer_character
    (χ : AddChar ℝ ℂ) (hχ : ∀ z : ℤ, χ (z : ℝ) = 1)
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B)
    (z β : B → ℤ) (Q : MvPolynomial B ℤ) :
    χ (translationPhaseArgument D₀
      (g * ⟨fun i => (z i : ℝ), MvPolynomial.map (Int.castRingHom ℝ) Q⟩)
      (fun i => ((β i + z i : ℤ) : ℝ))) =
        χ (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) := by
  have hβ : (fun i => ((β i + z i : ℤ) : ℝ)) =
      (fun i => (β i : ℝ)) + (fun i => (z i : ℝ)) := by ext i; simp
  rw [hβ, translationPhaseArgument_mul, χ.map_add_eq_mul]
  have hQ : eval ((fun i => (β i : ℝ)) + (fun i => (z i : ℝ)))
      (MvPolynomial.map (Int.castRingHom ℝ) Q) = (eval (β + z) Q : ℝ) := by
    change eval (fun i => (β i : ℝ) + (z i : ℝ)) _ = _
    simpa only [Pi.add_apply, Int.cast_add] using eval_integer_polynomial_real Q (β + z)
  rw [hQ, hχ, mul_one]

theorem translationPhaseArgument_majorSymbol
    (D : MvPolynomial (U ⊕ B) ℝ) (D₀ : MvPolynomial B ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (β : B → ℝ) :
    translationPhaseArgument D₀ (algebraicMajorSymbol D D₀ A u) β =
      eval (Sum.elim u β) D := by
  simp only [translationPhaseArgument, algebraicMajorSymbol, map_sub,
    polynomialTranslate_eval_ring, specializeMajorParameters_eval]
  have he : (fun i => β i + -eval u (A i)) = β - (fun i => eval u (A i)) := by
    ext i; simp [sub_eq_add_neg]
  rw [he]
  exact sub_add_cancel _ _

theorem translationPhaseArgument_fourier_integer
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B)
    (z β : B → ℤ) (Q : MvPolynomial B ℤ) :
    (Real.fourierChar (translationPhaseArgument D₀
      (g * ⟨fun i => (z i : ℝ), MvPolynomial.map (Int.castRingHom ℝ) Q⟩)
      (fun i => ((β i + z i : ℤ) : ℝ))) : ℂ) =
        (Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) : ℂ) := by
  apply translationPhaseArgument_integer_character
    (Circle.coeHom.compAddChar Real.fourierChar) ?_
  intro z
  change (Circle.exp (2 * Real.pi * (z : ℝ)) : ℂ) = 1
  rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
  simp

noncomputable def translationPhaseFunction (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B) : ℂ :=
  Real.fourierChar (translationPhaseArgument D₀ g (fun i => (⌊g.base i + 1 / 2⌋ : ℝ)))

theorem translationPhaseFunction_integer_lattice
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B)
    (z : B → ℤ) (Q : MvPolynomial B ℤ) :
    translationPhaseFunction D₀
      (g * ⟨fun i => (z i : ℝ), MvPolynomial.map (Int.castRingHom ℝ) Q⟩) =
        translationPhaseFunction D₀ g := by
  unfold translationPhaseFunction
  have hfloor (i : B) : ⌊(g.base i + (z i : ℝ)) + 1 / 2⌋ =
      ⌊g.base i + 1 / 2⌋ + z i := by
    rw [show g.base i + (z i : ℝ) + 1 / 2 = (g.base i + 1 / 2) + z i by ring,
      Int.floor_add_intCast]
  simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply, hfloor]
  exact translationPhaseArgument_fourier_integer D₀ g z (fun i => ⌊g.base i + 1 / 2⌋) Q

theorem translationPhaseFunction_central
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B) (a : ℝ) :
    translationPhaseFunction D₀ (g * ⟨0, C a⟩) =
      translationPhaseFunction D₀ g * (Real.fourierChar a : ℂ) := by
  unfold translationPhaseFunction
  have hb : (g * (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ B)).base = g.base := by
    simp
  rw [hb]
  have ha := translationPhaseArgument_mul D₀ g
    (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ B) (fun i => (⌊g.base i + 1 / 2⌋ : ℝ))
  simp only [add_zero, eval_C] at ha
  rw [ha, Real.fourierChar.map_add_eq_mul]
  rfl

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {U X : Type*}

theorem real_grid_polynomial_residue_difference (R : MvPolynomial U ℝ)
    (q : ℕ) (hq : 0 < q) (hR : realPolynomialCoefficientGrid q R)
    (r v : U → ℤ) :
    ∃ k : ℤ,
      eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) R -
        eval (fun i => (r i : ℝ)) R = (k : ℝ) := by
  obtain ⟨S, hS⟩ := (realPolynomialCoefficientGrid_iff q R).mp hR
  have heval (y : U → ℤ) : (eval y S : ℝ) =
      (q : ℝ) * eval (fun i => (y i : ℝ)) R := by
    rw [← eval_integer_polynomial_real, hS, map_mul, eval_C]
  obtain ⟨k, hk⟩ := integer_polynomial_sub_dvd S
    (fun i => r i + (q : ℤ) * v i) r (q : ℤ) (fun i => by
      exact ⟨v i, by ring⟩)
  refine ⟨k, ?_⟩
  apply mul_left_cancel₀ (show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne')
  calc
    (q : ℝ) * (eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) R -
        eval (fun i => (r i : ℝ)) R) =
        ((eval (fun i => r i + (q : ℤ) * v i) S - eval r S : ℤ) : ℝ) := by
      rw [Int.cast_sub, heval, heval, mul_sub]
    _ = (q : ℝ) * (k : ℝ) := by exact_mod_cast hk

theorem real_fourierChar_add_integer (t : ℝ) (k : ℤ) :
    (Real.fourierChar (t + (k : ℝ)) : ℂ) = (Real.fourierChar t : ℂ) := by
  rw [Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
  have hk : (Real.fourierChar (k : ℝ) : ℂ) = 1 := by
    change (Circle.exp (2 * Real.pi * (k : ℝ)) : ℂ) = 1
    rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
    simp
  rw [hk, mul_one]

theorem real_fourierChar_sub_star (a b : ℝ) :
    (Real.fourierChar (a - b) : ℂ) =
      (Real.fourierChar a : ℂ) * star (Real.fourierChar b : ℂ) := by
  rw [Real.fourierChar.map_sub_eq_div, div_eq_mul_inv, Circle.coe_mul,
    Circle.coe_inv_eq_conj]
  rfl

noncomputable def residueAffinePolynomial (q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) : MvPolynomial U ℝ :=
  eval₂Hom C (fun i => C (r i : ℝ) + C (q : ℝ) * MvPolynomial.X i) P

theorem residueAffinePolynomial_eval (q : ℕ) (r v : U → ℤ)
    (P : MvPolynomial U ℝ) :
    eval (fun i => (v i : ℝ)) (residueAffinePolynomial q r P) =
      eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [residueAffinePolynomial]
  | add P Q hP hQ => simpa only [residueAffinePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [residueAffinePolynomial, map_mul, eval₂Hom_X', map_add, eval_C,
      eval_X, Int.cast_add, Int.cast_mul, Int.cast_natCast] at *
    rw [hP]

theorem residueAffinePolynomial_totalDegree_le (q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) (n : ℕ) (hP : P.totalDegree ≤ n) :
    (residueAffinePolynomial q r P).totalDegree ≤ n := by
  have hf (i : U) : (C (r i : ℝ) + C (q : ℝ) * MvPolynomial.X i).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp only [totalDegree_C]; omega
    · exact (totalDegree_mul _ _).trans (by
        simp only [totalDegree_C, totalDegree_X, Nat.zero_add, le_refl])
  simpa only [residueAffinePolynomial, Nat.mul_one] using
    polynomial_substitution_totalDegree_le P _ hf hP

noncomputable def localMajorLowerPhase (n q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) : MvPolynomial U ℝ :=
  residueAffinePolynomial q r (P - homogeneousComponent (n + 1) P)

theorem localMajorLowerPhase_totalDegree_le (n q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1) :
    (localMajorLowerPhase n q r P).totalDegree ≤ n :=
  residueAffinePolynomial_totalDegree_le q r _ n (totalDegree_sub_top_component_le n P hP)

theorem localMajorLowerPhase_cancellation (n q : ℕ) (hq : 0 < q)
    (r v : U → ℤ) (P E R : MvPolynomial U ℝ)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R) :
    (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) P) : ℂ) *
        star (Real.fourierChar (eval (fun i => (v i : ℝ))
          (localMajorLowerPhase n q r P)) : ℂ) =
      (Real.fourierChar
        (eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) E +
          eval (fun i => (r i : ℝ)) R) : ℂ) := by
  rw [show localMajorLowerPhase n q r P =
    residueAffinePolynomial q r (P - homogeneousComponent (n + 1) P) from rfl,
    residueAffinePolynomial_eval, map_sub, htop, map_add]
  rw [← real_fourierChar_sub_star]
  rw [sub_sub_cancel]
  obtain ⟨k, hk⟩ := real_grid_polynomial_residue_difference R q hq hR r v
  have hr : eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) R =
      eval (fun i => (r i : ℝ)) R + (k : ℝ) := by linarith
  rw [hr, ← add_assoc, real_fourierChar_add_integer]

theorem localMajorPhaseCorrelation [Fintype X]
    (p : FiniteProbabilityWeights X) (v : X → U → ℤ)
    (n q : ℕ) (hq : 0 < q) (r : U → ℤ)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R) (a ε : ℝ)
    (hslow : ∀ x, 0 < p.weight x →
      |eval (fun i => ((r i + (q : ℤ) * v x i : ℤ) : ℝ)) E - a| ≤ ε) :
    (localMajorLowerPhase n q r P).totalDegree ≤ n ∧
    1 - 2 * Real.pi * ε ≤ ‖p.complexMean (fun x =>
      (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * v x i : ℤ) : ℝ)) P) : ℂ) *
        star (Real.fourierChar (eval (fun i => (v x i : ℝ))
          (localMajorLowerPhase n q r P)) : ℂ))‖ := by
  refine ⟨localMajorLowerPhase_totalDegree_le n q r P hP, ?_⟩
  let f : X → ℂ := fun x =>
    (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * v x i : ℤ) : ℝ)) P) : ℂ) *
      star (Real.fourierChar (eval (fun i => (v x i : ℝ))
        (localMajorLowerPhase n q r P)) : ℂ)
  let c : ℂ := Real.fourierChar (a + eval (fun i => (r i : ℝ)) R)
  have hpoint (x : X) (hx : p.weight x ≠ 0) : ‖f x - c‖ ≤ 2 * Real.pi * ε := by
    dsimp only [f, c]
    rw [localMajorLowerPhase_cancellation n q hq r (v x) P E R htop hR]
    refine (real_fourierChar_norm_sub_le _ _).trans ?_
    rw [add_sub_add_right_eq_sub]
    exact mul_le_mul_of_nonneg_left (hslow x (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)))
      (by positivity)
  have havg := p.norm_complexMean_sub_le f (fun _ => c) (fun _ => 2 * Real.pi * ε) hpoint
  rw [p.complexMean_const, p.mean_const] at havg
  have hc : ‖c‖ = 1 := Circle.norm_coe _
  have hnorm := norm_le_norm_add_norm_sub (p.complexMean f) c
  rw [hc] at hnorm
  change 1 - 2 * Real.pi * ε ≤ ‖p.complexMean f‖
  linarith

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*}

noncomputable def floorIntegerPolynomial (D : MvPolynomial σ ℝ) : MvPolynomial σ ℤ :=
  .ofCoeff ((AddMonoidAlgebra.coeff D).mapRange Int.floor Int.floor_zero)

@[simp] theorem floorIntegerPolynomial_coeff (D : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    (floorIntegerPolynomial D).coeff a = ⌊D.coeff a⌋ := rfl

noncomputable def fractionalCoefficientPolynomial (D : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  D - MvPolynomial.map (Int.castRingHom ℝ) (floorIntegerPolynomial D)

@[simp] theorem fractionalCoefficientPolynomial_coeff (D : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    (fractionalCoefficientPolynomial D).coeff a = Int.fract (D.coeff a) := by
  simp only [fractionalCoefficientPolynomial, coeff_sub, coeff_map,
    floorIntegerPolynomial_coeff, Int.fract]
  rfl

theorem fractionalCoefficientPolynomial_bounds (D : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    0 ≤ (fractionalCoefficientPolynomial D).coeff a ∧
      (fractionalCoefficientPolynomial D).coeff a < 1 := by
  rw [fractionalCoefficientPolynomial_coeff]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem fractionalCoefficientPolynomial_isWeightedHomogeneous (D : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (hD : D.IsWeightedHomogeneous w d) :
    (fractionalCoefficientPolynomial D).IsWeightedHomogeneous w d := by
  intro a ha
  apply hD
  intro hzero
  apply ha
  simp only [fractionalCoefficientPolynomial_coeff, hzero, Int.fract_zero]

theorem fractionalCoefficientPolynomial_mass_le_card (D : MvPolynomial σ ℝ) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((fractionalCoefficientPolynomial D).support.card : ℝ) := by
  classical
  calc
    _ ≤ ∑ _a ∈ (fractionalCoefficientPolynomial D).support, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_of_nonneg (fractionalCoefficientPolynomial_bounds D a).1]
      exact (fractionalCoefficientPolynomial_bounds D a).2.le
    _ = _ := by simp

theorem fractionalCoefficientPolynomial_mass_le [Fintype σ] (D : MvPolynomial σ ℝ)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (hD : D.IsWeightedHomogeneous w d) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((Fintype.card σ : ℝ) + 1) ^ d := by
  refine (fractionalCoefficientPolynomial_mass_le_card D).trans ?_
  have hcard := boundedExponentSet_card_le (fractionalCoefficientPolynomial D).support d
    (fun a ha => (exponentSum_le_positive_weight w hw a).trans
      (le_of_eq (fractionalCoefficientPolynomial_isWeightedHomogeneous D w d hD
        (mem_support_iff.mp ha))))
  exact_mod_cast hcard

theorem floorIntegerPolynomial_add_fractionalCoefficientPolynomial (D : MvPolynomial σ ℝ) :
    MvPolynomial.map (Int.castRingHom ℝ) (floorIntegerPolynomial D) +
      fractionalCoefficientPolynomial D = D := by
  exact add_sub_cancel _ _

theorem fractionalCoefficientPolynomial_fourierChar (D : MvPolynomial σ ℝ) (z : σ → ℤ) :
    Real.fourierChar (eval (fun i => (z i : ℝ)) (fractionalCoefficientPolynomial D)) =
      Real.fourierChar (eval (fun i => (z i : ℝ)) D) := by
  have h := congrArg (fun P => Real.fourierChar (eval (fun i => (z i : ℝ)) P))
    (floorIntegerPolynomial_add_fractionalCoefficientPolynomial D)
  have hz : Real.fourierChar ((eval z (floorIntegerPolynomial D) : ℤ) : ℝ) = 1 := by
    apply Subtype.ext
    change (Circle.exp (2 * Real.pi * ((eval z (floorIntegerPolynomial D) : ℤ) : ℝ)) : ℂ) = 1
    rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
    simp
  simpa only [map_add, eval_integer_polynomial_real, Real.fourierChar.map_add_eq_mul,
    hz, one_mul] using h

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {B : Type*}

theorem translationPhaseArgument_left_increment
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) :
    translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β =
      eval (β - g.base) z.polynomial +
        (eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀) := by
  simp only [translationPhaseArgument, PolynomialTranslationGroupOver.polynomial_mul,
    PolynomialTranslationGroupOver.base_mul, map_add, polynomialTranslate_eval_ring]
  have h₁ : (fun i => β i + (-g.base) i) = β - g.base := by ext i; simp [sub_eq_add_neg]
  have h₂ : β - (z.base + g.base) = β - g.base - z.base := by abel
  rw [h₁, h₂]
  ring

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {B : Type*}

noncomputable def integerPolynomialTranslationSubgroup :
    Subgroup (PolynomialTranslationGroupOver ℝ B) :=
  (PolynomialTranslationGroupOver.map (B := B) (Int.castRingHom ℝ)).range

theorem translationPhaseFunction_integerSubgroup
    (D₀ : MvPolynomial B ℝ) (g γ : PolynomialTranslationGroupOver ℝ B)
    (hγ : γ ∈ integerPolynomialTranslationSubgroup) :
    translationPhaseFunction D₀ (g * γ) = translationPhaseFunction D₀ g := by
  obtain ⟨γ, rfl⟩ := hγ
  exact translationPhaseFunction_integer_lattice D₀ g γ.base γ.polynomial

noncomputable def translationQuotientPhase (D₀ : MvPolynomial B ℝ) :
    (PolynomialTranslationGroupOver ℝ B ⧸ integerPolynomialTranslationSubgroup) → ℂ :=
  Quotient.lift (translationPhaseFunction D₀) (fun g h hgh => by
    have hi := translationPhaseFunction_integerSubgroup D₀ g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

@[simp] theorem translationQuotientPhase_mk (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B) :
    translationQuotientPhase D₀ (QuotientGroup.mk g) = translationPhaseFunction D₀ g := rfl

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialDerivationDrop (w : σ → ℕ) (k : ℕ) :
    Submodule R (Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) where
  carrier := {D | ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k}
  zero_mem' := by
    intro i
    exact Submodule.zero_mem _
  add_mem' := by
    intro D E hD hE i
    exact (weightedSupportDrop w (w i) k).add_mem (hD i) (hE i)
  smul_mem' := by
    intro c D hD i
    exact (weightedSupportDrop w (w i) k).smul_mem c (hD i)

theorem polynomialDerivationDrop_antitone (w : σ → ℕ) :
    Antitone (polynomialDerivationDrop (R := R) w) := by
  intro a b hab D hD i
  exact weightedSupportDrop_antitone hab (hD i)

theorem polynomialDerivationDrop_bracket (w : σ → ℕ) (a b : ℕ)
    {D E : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)}
    (hD : D ∈ polynomialDerivationDrop w a) (hE : E ∈ polynomialDerivationDrop w b) :
    ⁅D, E⁆ ∈ polynomialDerivationDrop w (a + b) :=
  weightedDerivation_bracket w D E a b hD hE

noncomputable def polynomialLoweringLieAlgebra (w : σ → ℕ) :
    LieSubalgebra R (Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) :=
  { polynomialDerivationDrop w 1 with
    lie_mem' := fun hD hE => polynomialDerivationDrop_antitone w (by decide : 1 ≤ 1 + 1)
      (polynomialDerivationDrop_bracket w 1 1 hD hE) }

abbrev PolynomialShearLieAlgebra (w : σ → ℕ) (R : Type*) [CommRing R] :=
  ↥(polynomialLoweringLieAlgebra (R := R) w)

noncomputable def polynomialShearLayer (w : σ → ℕ) (k : ℕ) :
    Submodule R (PolynomialShearLieAlgebra w R) :=
  (polynomialDerivationDrop w k).comap (polynomialLoweringLieAlgebra w).incl.toLinearMap

theorem polynomialShearLayer_antitone (w : σ → ℕ) :
    Antitone (polynomialShearLayer (R := R) w) := by
  intro a b hab D hD
  exact polynomialDerivationDrop_antitone w hab hD

theorem polynomialShearLayer_one (w : σ → ℕ) :
    polynomialShearLayer (R := R) w 1 = ⊤ := by
  apply top_unique
  intro D _
  exact D.property

theorem polynomialShearLayer_bracket (w : σ → ℕ) (a b : ℕ)
    {D E : PolynomialShearLieAlgebra w R}
    (hD : D ∈ polynomialShearLayer (R := R) w a)
    (hE : E ∈ polynomialShearLayer (R := R) w b) :
    ⁅D, E⁆ ∈ polynomialShearLayer (R := R) w (a + b) :=
  polynomialDerivationDrop_bracket w a b hD hE

theorem polynomialShearLayer_terminal (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    polynomialShearLayer (R := R) w (s + 1) = ⊥ := by
  apply bot_unique
  intro D hD
  change D = 0
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  change D.val (X i) = 0
  exact weightedSupportDrop_eq_zero (Nat.lt_succ_of_le (hw i)) (hD i)

noncomputable def polynomialShearFiltration (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    NilpotentLieFiltration (PolynomialShearLieAlgebra w ℚ) s where
  layer := polynomialShearLayer w
  antitone := polynomialShearLayer_antitone w
  one_eq_top := polynomialShearLayer_one w
  lie_mem := polynomialShearLayer_bracket w _ _
  terminal := polynomialShearLayer_terminal w s hw

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

abbrev PolynomialShearIndex (w : σ → ℕ) :=
  Σ i : σ, {a : σ →₀ ℕ // Finsupp.weight w a + 1 ≤ w i}

noncomputable def polynomialShearCoordinates (w : σ → ℕ) :
    PolynomialShearLieAlgebra w R ≃ₗ[R] (i : σ) → weightedSupportDrop (R := R) w (w i) 1 where
  toFun D i := ⟨D.val (X i), D.property i⟩
  invFun f := ⟨MvPolynomial.mkDerivation R (fun i => (f i : MvPolynomial σ R)), by
    intro i
    rw [MvPolynomial.mkDerivation_X]
    exact (f i).property⟩
  left_inv D := by
    apply Subtype.ext
    apply MvPolynomial.derivation_ext
    intro i
    exact MvPolynomial.mkDerivation_X _ _ _
  right_inv f := by
    funext i
    apply Subtype.ext
    exact MvPolynomial.mkDerivation_X _ _ _
  map_add' D E := by
    funext i
    apply Subtype.ext
    rfl
  map_smul' c D := by
    funext i
    apply Subtype.ext
    rfl

noncomputable def polynomialShearBasis [Fintype σ] (w : σ → ℕ) :
    Basis (PolynomialShearIndex w) R (PolynomialShearLieAlgebra w R) :=
  (Pi.basis (fun i => MvPolynomial.basisRestrictSupport R
    {a : σ →₀ ℕ | Finsupp.weight w a + 1 ≤ w i})).map (polynomialShearCoordinates w).symm

theorem polynomialShearBasis_repr [Fintype σ] (w : σ → ℕ)
    (D : PolynomialShearLieAlgebra w R) (a : PolynomialShearIndex w) :
    (polynomialShearBasis (R := R) w).repr D a = (D.val (X a.1)).coeff a.2.val := rfl

noncomputable def polynomialShearMonomial (w : σ → ℕ) (a : PolynomialShearIndex w) :
    PolynomialShearLieAlgebra w R := by
  classical
  refine ⟨MvPolynomial.mkDerivation R (Pi.single a.1 (monomial a.2.val 1)), ?_⟩
  intro i
  rw [MvPolynomial.mkDerivation_X]
  by_cases h : i = a.1
  · subst i
    rw [Pi.single_eq_same]
    exact (MvPolynomial.monomial_mem_restrictSupport R).mpr (Or.inl a.2.property)
  · rw [Pi.single_eq_of_ne h]
    exact Submodule.zero_mem _

theorem polynomialShearMonomial_X [DecidableEq σ] (w : σ → ℕ) (a : PolynomialShearIndex w) (i : σ) :
    (polynomialShearMonomial (R := R) w a).val (X i) =
      if i = a.1 then monomial a.2.val 1 else 0 := by
  classical
  rw [polynomialShearMonomial, MvPolynomial.mkDerivation_X]
  by_cases h : i = a.1
  · subst i
    simp only [Pi.single_eq_same, ite_true]
  · simp [h]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialShearBoundedCoordinates (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) :
    PolynomialShearLieAlgebra w R →ₗ[R] (σ → weightedSupportLE (R := R) w s) where
  toFun D i := ⟨D.val (X i), weightedSupportLE_mono (hw i)
    (weightedSupportDrop_le (D.property i))⟩
  map_add' D E := by
    funext i
    apply Subtype.ext
    rfl
  map_smul' c D := by
    funext i
    apply Subtype.ext
    rfl

theorem polynomialShearBoundedCoordinates_injective (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) :
    Function.Injective (polynomialShearBoundedCoordinates (R := R) w s hw) := by
  intro D E h
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  exact congrArg (fun f : σ → weightedSupportLE (R := R) w s => (f i : MvPolynomial σ R)) h

theorem polynomialShear_finrank_le {K : Type*} [Field K] [Fintype σ]
    (w : σ → ℕ) (hwpos : ∀ i, 0 < w i) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    finrank K (PolynomialShearLieAlgebra w K) ≤ Fintype.card σ * (Fintype.card σ + 1) ^ s := by
  let : Module.Finite K (weightedSupportLE (R := K) w s) := weightedSupportLE_moduleFinite w hwpos s
  calc
    _ ≤ finrank K (σ → weightedSupportLE (R := K) w s) :=
      LinearMap.finrank_le_finrank_of_injective
        (polynomialShearBoundedCoordinates_injective (R := K) w s hw)
    _ = ∑ _i : σ, finrank K (weightedSupportLE (R := K) w s) := Module.finrank_pi_fintype K
    _ = Fintype.card σ * finrank K (weightedSupportLE (R := K) w s) := by simp
    _ ≤ Fintype.card σ * (Fintype.card σ + 1) ^ s :=
      Nat.mul_le_mul_left _ (weightedSupportLE_finrank_le (K := K) w hwpos s)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

theorem polynomialShear_X_mass_of_coordinates (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {s : ℕ} (hw : ∀ i, w i ≤ s)
    {δ : ℝ} (hδ : 0 ≤ δ) (hD : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr D a| ≤ δ) (i : σ) :
    realPolynomialMass (D.val (X i)) ≤ ((s + 1) * (Fintype.card σ + 1) ^ s : ℕ) * δ := by
  classical
  have hdegree : (D.val (X i)).totalDegree ≤ s :=
    totalDegree_le_of_positive_weightedSupport w hpos
      (weightedSupportLE_mono (hw i) (weightedSupportDrop_le (D.property i)))
  calc
    _ ≤ ∑ _a ∈ (D.val (X i)).support, δ := by
      apply Finset.sum_le_sum
      intro a ha
      exact hD ⟨i, a, D.property i ha⟩
    _ = ((D.val (X i)).support.card : ℝ) * δ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast polynomial_support_card_le _ hdegree) hδ

omit [Fintype σ] in
theorem polynomialShear_pow_degree (D : PolynomialShearLieAlgebra w ℝ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    (D.val.toLinearMap ^ k) P ∈ weightedSupportLE w n := by
  have h := weightedDerivation_pow w D.val 1 D.property
    (show P ∈ weightedSupportDrop w n 0 by rwa [weightedSupportDrop_zero]) k
  exact weightedSupportDrop_le h

theorem polynomialShear_pow_mass (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {M : ℝ} (hM : 0 ≤ M)
    (hD : ∀ i, realPolynomialMass (D.val (X i)) ≤ M)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    realPolynomialMass ((D.val.toLinearMap ^ k) P) ≤
      (Fintype.card σ * M * n) ^ k * realPolynomialMass P := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hdegree := totalDegree_le_of_positive_weightedSupport w hpos
        (polynomialShear_pow_degree D hP k)
      apply (realPolynomialMass_derivation D.val hM hD hdegree).trans
      calc
        _ ≤ (Fintype.card σ * M * n) *
            ((Fintype.card σ * M * n) ^ k * realPolynomialMass P) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by rw [pow_succ']; ring

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

noncomputable def polynomialShearEnd (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    Module.End R (weightedSupportLE (R := R) w n) where
  toFun P := ⟨D.val P, weightedSupportDrop_le
    (weightedDerivation_apply_le w D.val 1 D.property P.property)⟩
  map_add' P Q := by
    apply Subtype.ext
    exact D.val.map_add P Q
  map_smul' c P := by
    apply Subtype.ext
    exact D.val.map_smul c P

noncomputable def polynomialShearAction (w : σ → ℕ) (n : ℕ) :
    PolynomialShearLieAlgebra w R →ₗ⁅R⁆ Module.End R (weightedSupportLE (R := R) w n) where
  toLinearMap :=
    { toFun := fun D => polynomialShearEnd D n
      map_add' := by
        intro D E
        apply LinearMap.ext
        intro P
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c D
        apply LinearMap.ext
        intro P
        apply Subtype.ext
        rfl }
  map_lie' := by
    intro D E
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    rfl

theorem polynomialShearEnd_pow_coe (D : PolynomialShearLieAlgebra w R) (n k : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    ((polynomialShearEnd D n ^ k) P : MvPolynomial σ R) =
      (D.val.toLinearMap ^ k) (P : MvPolynomial σ R) := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl

theorem polynomialShearEnd_pow_eq_zero (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    polynomialShearEnd D n ^ (n + 1) = 0 := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  change ((polynomialShearEnd D n ^ (n + 1)) P : MvPolynomial σ R) = 0
  rw [polynomialShearEnd_pow_coe]
  exact weightedDerivation_pow_eq_zero w D.val D.property P.property

theorem polynomialShearEnd_isNilpotent (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    IsNilpotent (polynomialShearEnd D n) := ⟨n + 1, polynomialShearEnd_pow_eq_zero D n⟩

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R] [Fintype σ]

theorem polynomialShearMonomial_repr (w : σ → ℕ) (a : PolynomialShearIndex w) :
    (polynomialShearBasis (R := R) w).repr (polynomialShearMonomial (R := R) w a) =
      Finsupp.single a 1 := by
  classical
  ext b
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rw [polynomialShearBasis_repr, polynomialShearMonomial_X]
  by_cases hij : j = i
  · subst j
    by_cases hab : a = b
    · subst b
      simp
    · have hval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      simp [hab, hval]
  · simp [hij]

theorem polynomialShearBasis_eq_monomial (w : σ → ℕ) (a : PolynomialShearIndex w) :
    polynomialShearBasis (R := R) w a = polynomialShearMonomial w a := by
  apply (polynomialShearBasis (R := R) w).repr.injective
  rw [Basis.repr_self, polynomialShearMonomial_repr]

noncomputable def polynomialShearDeficit (w : σ → ℕ) (a : PolynomialShearIndex w) : ℕ :=
  w a.1 - Finsupp.weight w a.2.val

theorem polynomialShearBasis_mem_layer (w : σ → ℕ) (a : PolynomialShearIndex w) (r : ℕ)
    (hr : r ≤ polynomialShearDeficit w a) :
    polynomialShearBasis (R := R) w a ∈ polynomialShearLayer (R := R) w r := by
  classical
  rw [polynomialShearBasis_eq_monomial]
  intro i
  change (polynomialShearMonomial (R := R) w a).val (X i) ∈ weightedSupportDrop w (w i) r
  rw [polynomialShearMonomial_X]
  by_cases hi : i = a.1
  · subst i
    rw [if_pos rfl]
    apply (MvPolynomial.monomial_mem_restrictSupport R).mpr
    left
    change Finsupp.weight w a.2.val + r ≤ w a.1
    have h := a.2.property
    unfold polynomialShearDeficit at hr
    omega
  · rw [if_neg hi]
    exact Submodule.zero_mem _

theorem polynomialShearLayer_span (w : σ → ℕ) (r : ℕ) :
    polynomialShearLayer (R := R) w r =
      Submodule.span R (polynomialShearBasis (R := R) w '' {a | r ≤ polynomialShearDeficit w a}) := by
  classical
  apply le_antisymm
  · intro D hD
    apply (polynomialShearBasis (R := R) w).mem_span_image.mpr
    intro a ha
    have hc : (D.val (X a.1)).coeff a.2.val ≠ 0 := by
      simpa only [polynomialShearBasis_repr] using Finsupp.mem_support_iff.mp ha
    have h : Finsupp.weight w a.2.val + r ≤ w a.1 :=
      hD a.1 (MvPolynomial.mem_support_iff.mpr hc)
    change r ≤ w a.1 - Finsupp.weight w a.2.val
    omega
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact polynomialShearBasis_mem_layer w a r ha

@[instance_reducible]
noncomputable def polynomialShearIndexFintype (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Fintype (PolynomialShearIndex w) := by
  classical
  have hfinite (i : σ) : {a : σ →₀ ℕ | Finsupp.weight w a + 1 ≤ w i}.Finite :=
    (Finsupp.finite_of_nat_weight_le w (fun j => (hw j).ne') (w i)).subset
      (fun a ha => (Nat.le_add_right (Finsupp.weight w a) 1).trans ha)
  letI (i : σ) : Fintype {a : σ →₀ ℕ // Finsupp.weight w a + 1 ≤ w i} := (hfinite i).fintype
  exact inferInstance

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def polynomialShearExpOn (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    Module.End R (weightedSupportLE (R := R) w n) :=
  IsNilpotent.exp (polynomialShearEnd D n)

theorem polynomialShearExpOn_sum (D : PolynomialShearLieAlgebra w R) (n : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    (polynomialShearExpOn D n P : MvPolynomial σ R) =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℚ)⁻¹ •
        (D.val.toLinearMap ^ k) (P : MvPolynomial σ R) := by
  simp [polynomialShearExpOn, IsNilpotent.exp_eq_sum (a := polynomialShearEnd D n) (polynomialShearEnd_pow_eq_zero D n),
    polynomialShearEnd_pow_coe]

theorem polynomialShearExpOn_mono (D : PolynomialShearLieAlgebra w R)
    {m n : ℕ} (hmn : m ≤ n) (P : weightedSupportLE (R := R) w m) :
    (polynomialShearExpOn D n ⟨P.val, weightedSupportLE_mono hmn P.property⟩ :
      MvPolynomial σ R) = (polynomialShearExpOn D m P : MvPolynomial σ R) := by
  let inc : weightedSupportLE (R := R) w m →ₗ[R] weightedSupportLE (R := R) w n :=
    Submodule.inclusion (fun _ h => weightedSupportLE_mono hmn h)
  have hc : polynomialShearEnd D n ∘ₗ inc = inc ∘ₗ polynomialShearEnd D m := by
    ext Q
    rfl
  have h := Module.End.commute_exp_left_of_commute (polynomialShearEnd_isNilpotent D m)
    (polynomialShearEnd_isNilpotent D n) hc
  exact congrArg Subtype.val (LinearMap.congr_fun h P)

noncomputable def weightedPolynomialMul (w : σ → ℕ) (m n : ℕ) :
    weightedSupportLE (R := R) w m →ₗ[R]
      weightedSupportLE (R := R) w n →ₗ[R] weightedSupportLE (R := R) w (m + n) where
  toFun P :=
    { toFun := fun Q => ⟨P.val * Q.val, weightedSupportLE_mul P.property Q.property⟩
      map_add' := fun Q T => Subtype.ext (mul_add P.val Q.val T.val)
      map_smul' := fun c Q => Subtype.ext (mul_smul_comm c P.val Q.val) }
  map_add' P Q := by
    apply LinearMap.ext
    intro T
    exact Subtype.ext (add_mul P.val Q.val T.val)
  map_smul' c P := by
    apply LinearMap.ext
    intro Q
    exact Subtype.ext (smul_mul_assoc c P.val Q.val)

theorem polynomialShearExpOn_mul (D : PolynomialShearLieAlgebra w R) (m n : ℕ)
    (P : weightedSupportLE (R := R) w m) (Q : weightedSupportLE (R := R) w n) :
    (polynomialShearExpOn D (m + n) (weightedPolynomialMul w m n P Q) : MvPolynomial σ R) =
      (polynomialShearExpOn D m P : MvPolynomial σ R) *
        (polynomialShearExpOn D n Q : MvPolynomial σ R) := by
  have h := nilpotentExp_bilinear (weightedPolynomialMul (R := R) w m n)
    (polynomialShearEnd D m) (polynomialShearEnd D n) (polynomialShearEnd D (m + n))
    (polynomialShearEnd_isNilpotent D m) (polynomialShearEnd_isNilpotent D n)
    (polynomialShearEnd_isNilpotent D (m + n))
    (fun x y => Subtype.ext (by
      change D.val (x.val * y.val) = D.val x.val * y.val + x.val * D.val y.val
      rw [D.val.leibniz, smul_eq_mul, smul_eq_mul]
      ring)) P Q
  exact congrArg Subtype.val h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped BigOperators Classical

variable {σ R : Type*} [CommRing R] [Fintype σ]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def polynomialShearExp (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  polynomialShearExpOn D (P.weightedTotalDegree w)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩

theorem polynomialShearExp_eq_on (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P = (polynomialShearExpOn D n ⟨P, hP⟩ : MvPolynomial σ R) :=
  (polynomialShearExpOn_mono D ((mem_weightedSupportLE_iff w n P).mp hP)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩).symm

theorem polynomialShearExp_eq_sum (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P = ∑ k ∈ Finset.range (n + 1),
      (k.factorial : ℚ)⁻¹ • (D.val.toLinearMap ^ k) P := by
  rw [polynomialShearExp_eq_on D hP]
  exact polynomialShearExpOn_sum D n ⟨P, hP⟩

theorem polynomialShearExp_degree (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P ∈ weightedSupportLE w n := by
  rw [polynomialShearExp_eq_on D hP]
  exact (polynomialShearExpOn D n ⟨P, hP⟩).property

theorem polynomialShearExp_add (D : PolynomialShearLieAlgebra w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearExp D (P + Q) = polynomialShearExp D P + polynomialShearExp D Q := by
  let n := P.weightedTotalDegree w + Q.weightedTotalDegree w
  have hp : P ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n P).mpr (Nat.le_add_right _ _)
  have hq : Q ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n Q).mpr (Nat.le_add_left _ _)
  rw [polynomialShearExp_eq_on D ((weightedSupportLE w n).add_mem hp hq),
    polynomialShearExp_eq_on D hp, polynomialShearExp_eq_on D hq]
  exact congrArg Subtype.val ((polynomialShearExpOn D n).map_add ⟨P, hp⟩ ⟨Q, hq⟩)

theorem polynomialShearExp_mul (D : PolynomialShearLieAlgebra w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearExp D (P * Q) = polynomialShearExp D P * polynomialShearExp D Q := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  have hq : Q ∈ weightedSupportLE w (Q.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ Q).mpr le_rfl
  rw [polynomialShearExp_eq_on D (weightedSupportLE_mul hp hq),
    polynomialShearExp_eq_on D hp, polynomialShearExp_eq_on D hq]
  exact polynomialShearExpOn_mul D _ _ ⟨P, hp⟩ ⟨Q, hq⟩

theorem polynomialShearExp_C (D : PolynomialShearLieAlgebra w R) (c : R) :
    polynomialShearExp D (C c) = C c := by
  rw [polynomialShearExp_eq_sum D (weightedSupportLE_C w 0 c)]
  simp

noncomputable def polynomialShearExpHom (D : PolynomialShearLieAlgebra w R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R where
  toFun := polynomialShearExp D
  map_one' := by simpa using polynomialShearExp_C D 1
  map_zero' := by simpa using polynomialShearExp_C D 0
  map_add' := polynomialShearExp_add D
  map_mul' := polynomialShearExp_mul D
  commutes' := polynomialShearExp_C D

theorem polynomialShearExp_sub_lower (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P - P ∈ weightedSupportLT w n := by
  rw [polynomialShearExp_eq_sum D hP, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
    one_smul, add_sub_cancel_right]
  apply (weightedSupportLT w n).sum_mem
  intro k hk
  have h := weightedDerivation_pow w D.val 1 D.property
    (show P ∈ weightedSupportDrop w n 0 by rwa [weightedSupportDrop_zero]) (k + 1)
  simp only [Nat.mul_one, Nat.zero_add] at h
  have hlow : (D.val.toLinearMap ^ (k + 1)) P ∈ weightedSupportLT w n := by
    rw [← weightedSupportDrop_one]
    exact weightedSupportDrop_antitone (Nat.le_add_left 1 k) h
  exact (weightedSupportLT (R := R) w n).restrictScalars ℚ |>.smul_mem _ hlow

noncomputable def polynomialShearExpAut (D : PolynomialShearLieAlgebra w R) :
    WeightedLoweringAut w R :=
  WeightedLoweringAut.ofHom w (polynomialShearExpHom D)
    (fun i => polynomialShearExp_sub_lower D (weightedSupportLE_X w i))

theorem polynomialShearExpAut_apply (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) : (polynomialShearExpAut D).val P = polynomialShearExp D P := rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearExp_eq_add_of_sq_eq_zero (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} (hP : (D.val.toLinearMap ^ 2) P = 0) :
    polynomialShearExp D P = P + D.val P := by
  let n := max (P.weightedTotalDegree w) 1
  have hdeg : P ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n P).mpr (le_max_left _ _)
  have htwo : 2 ≤ n + 1 := Nat.succ_le_succ (le_max_right _ _)
  rw [polynomialShearExp_eq_sum D hdeg]
  have hsum :
      (∑ k ∈ Finset.range 2, (k.factorial : ℚ)⁻¹ • (D.val.toLinearMap ^ k) P) =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℚ)⁻¹ • (D.val.toLinearMap ^ k) P := by
    apply Finset.sum_subset (Finset.range_mono htwo)
    intro k _ hk
    have hk2 : 2 ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
    rw [Module.End.pow_map_zero_of_le hk2 hP, smul_zero]
  rw [← hsum]
  simp [Finset.sum_range_succ]

theorem polynomialShearExp_X_of_derivation_eq_C (D : PolynomialShearLieAlgebra w R)
    (i : σ) (b : R) (hD : D.val (X i) = C b) :
    polynomialShearExp D (X i) = X i + C b := by
  have hsq : (D.val.toLinearMap ^ 2) (X i) = 0 := by
    change D.val (D.val (X i)) = 0
    rw [hD, MvPolynomial.derivation_C]
  rw [polynomialShearExp_eq_add_of_sq_eq_zero D hsq, hD]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def residualCoordinate (A : PolynomialSlots σ d w) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin d) ℝ := X (Sum.inr i) - slotPolynomialLift i (A.center i)

noncomputable def residualHom (A : PolynomialSlots σ d w) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (σ ⊕ Fin d) ℝ := aeval A.residualCoordinate

theorem residualHom_X (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualHom (X i) = A.residualCoordinate i := by
  simp only [residualHom, aeval_X]

theorem residualCoordinate_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualCoordinate i ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w i) :=
  (weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ (Sum.inr i))
    (slotPolynomialLift_degree (fun _ => 1) w i (A.degree i))

theorem residualCoordinate_slot_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualCoordinate i ∈ weightedSupportLE (Sum.elim (fun _ : σ => 0) w) (w i) := by
  apply weightedSupportLE_of_weight_le _ (A.residualCoordinate_degree i)
  intro a
  cases a <;> simp

theorem residualCoordinate_sub_topPart_lower (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualCoordinate i - A.topPart.residualCoordinate i ∈
      weightedSupportLT (Sum.elim (fun _ : σ => 0) w) (w i) := by
  have he : A.residualCoordinate i - A.topPart.residualCoordinate i =
      -slotPolynomialLift i (A.center i - A.topPart.center i) := by
    simp only [residualCoordinate, slotPolynomialLift, map_sub]
    abel
  rw [he]
  exact (weightedSupportLT _ _).neg_mem
    (slotPolynomialLift_lower (fun _ => 0) w i (A.sub_topPart_lower i))

theorem residualHom_sub_topPart_lower (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.residualHom p - A.topPart.residualHom p ∈
      weightedSupportLT (Sum.elim (fun _ : σ => 0) w) n := by
  apply weightedComparison_difference w _ A.residualHom A.topPart.residualHom _ _ _ hp
  · intro i
    rw [residualHom_X]
    exact A.residualCoordinate_slot_degree i
  · intro i
    rw [residualHom_X]
    exact A.topPart.residualCoordinate_slot_degree i
  · intro i
    rw [residualHom_X, residualHom_X]
    exact A.residualCoordinate_sub_topPart_lower i

theorem residualCoordinate_eval (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (b : Fin d → ℝ) (i : Fin d) :
    aeval (Sum.elim t b) (A.residualCoordinate i) =
      b i - (A.slots t).center b i := by
  rw [residualCoordinate, map_sub, aeval_X, slotPolynomialLift_eval]
  rfl

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualShift_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    rename (earlierSlot i) (-A.topPart.specializeCenter 0 i) ∈ weightedSupportLE w (w i) := by
  simpa only [map_neg] using (weightedSupportLE w (w i)).neg_mem
    (A.topPart.specializeCenter_full_degree 0 i)

noncomputable def topResidualEquiv (A : PolynomialSlots σ d w) :
    MvPolynomial (Fin d) ℝ ≃ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  triangularPolynomialEquiv w (fun i => -A.topPart.specializeCenter 0 i) A.topResidualShift_degree

theorem topResidualEquiv_X (A : PolynomialSlots σ d w) (i : Fin d) :
    A.topResidualEquiv (X i) = X i - rename (earlierSlot i) (A.topPart.specializeCenter 0 i) := by
  rw [topResidualEquiv, triangularPolynomialEquiv_X, map_neg, ← sub_eq_add_neg]

theorem topResidualEquiv_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.topResidualEquiv p ∈ weightedSupportLE w n :=
  triangularPolynomialEquiv_degree w _ A.topResidualShift_degree hp

theorem topResidualEquiv_inverse_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.topResidualEquiv.symm p ∈ weightedSupportLE w n :=
  triangularPolynomialEquiv_inverse_degree w _ A.topResidualShift_degree hp

theorem topResidualEquiv_lift (A : PolynomialSlots σ d w) :
    (rename (Sum.inr : Fin d → σ ⊕ Fin d)).comp A.topResidualEquiv.toAlgHom =
      A.topPart.residualHom := by
  apply MvPolynomial.algHom_ext
  intro i
  change rename Sum.inr (A.topResidualEquiv (X i)) = A.topPart.residualHom (X i)
  rw [topResidualEquiv_X, map_sub, rename_X, residualHom_X, residualCoordinate,
    topPart_lift_specialize]

noncomputable def loweringHom (A : PolynomialSlots σ d w) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (σ ⊕ Fin d) ℝ :=
  A.residualHom.comp A.topResidualEquiv.symm.toAlgHom

theorem loweringHom_comp_top (A : PolynomialSlots σ d w) :
    A.loweringHom.comp A.topResidualEquiv.toAlgHom = A.residualHom := by
  apply AlgHom.ext
  intro p
  change A.residualHom (A.topResidualEquiv.symm (A.topResidualEquiv p)) = A.residualHom p
  rw [AlgEquiv.symm_apply_apply]

theorem loweringHom_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.loweringHom p ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n := by
  change A.residualHom (A.topResidualEquiv.symm p) ∈ _
  apply polynomialHom_preserves_weightedDegree w _ A.residualHom _
    (A.topResidualEquiv_inverse_degree hp)
  intro i
  rw [residualHom_X]
  exact A.residualCoordinate_degree i

theorem loweringHom_X_lower (A : PolynomialSlots σ d w) (i : Fin d) :
    A.loweringHom (X i) - X (Sum.inr i) ∈
      weightedSupportLT (Sum.elim (fun _ : σ => 0) w) (w i) := by
  have h := A.residualHom_sub_topPart_lower
    (A.topResidualEquiv_inverse_degree (weightedSupportLE_X w i))
  have he : A.topPart.residualHom (A.topResidualEquiv.symm (X i)) = X (Sum.inr i) := by
    rw [← A.topResidualEquiv_lift]
    change rename Sum.inr (A.topResidualEquiv (A.topResidualEquiv.symm (X i))) = _
    rw [AlgEquiv.apply_symm_apply, rename_X]
  rw [he] at h
  exact h

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

noncomputable def patchParameterSpecialization (t : σ → ℝ) :
    MvPolynomial (σ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  aeval (Sum.elim (fun a => C (t a)) X)

theorem patchParameterSpecialization_X_slot (t : σ → ℝ) (i : Fin d) :
    patchParameterSpecialization t (X (Sum.inr i)) = X i := by
  simp only [patchParameterSpecialization, aeval_X, Sum.elim_inr]

theorem patchParameterSpecialization_lower (v : σ → ℕ) (w : Fin d → ℕ) (t : σ → ℝ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ} (hP : P ∈ weightedSupportLT (Sum.elim v w) n) :
    patchParameterSpecialization t P ∈ weightedSupportLT w n := by
  apply weightedSupportLT_map _ _ (patchParameterSpecialization t) _ hP
  intro a
  cases a with
  | inl j =>
      simp only [patchParameterSpecialization, aeval_X, Sum.elim_inl]
      exact weightedSupportLE_C w (v j) (t j)
  | inr j =>
      rw [patchParameterSpecialization_X_slot]
      exact weightedSupportLE_X w j

theorem patchParameterSpecialization_eval (t : σ → ℝ) (b : Fin d → ℝ)
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    aeval b (patchParameterSpecialization t P) = aeval (Sum.elim t b) P := by
  rw [patchParameterSpecialization, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f P)
  funext a
  cases a with
  | inl j => simp only [Sum.elim_inl, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  | inr j => simp only [Sum.elim_inr, aeval_X]

namespace PolynomialSlots

variable {w : Fin d → ℕ}

noncomputable def loweringAtHom (A : PolynomialSlots σ d w) (t : σ → ℝ) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  (patchParameterSpecialization t).comp A.loweringHom

theorem loweringAtHom_lower (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    A.loweringAtHom t (X i) - X i ∈ weightedSupportLT w (w i) := by
  have h := patchParameterSpecialization_lower (fun _ => 0) w t (A.loweringHom_X_lower i)
  rw [map_sub, patchParameterSpecialization_X_slot] at h
  exact h

noncomputable def loweringAt (A : PolynomialSlots σ d w) (t : σ → ℝ) :
    WeightedLoweringAut w ℝ :=
  WeightedLoweringAut.ofHom w (A.loweringAtHom t) (A.loweringAtHom_lower t)

theorem loweringAt_comp_top (A : PolynomialSlots σ d w) (t : σ → ℝ) :
    (A.loweringAt t).val.toAlgHom.comp A.topResidualEquiv.toAlgHom =
      (patchParameterSpecialization t).comp A.residualHom := by
  apply AlgHom.ext
  intro P
  change patchParameterSpecialization t (A.loweringHom (A.topResidualEquiv P)) =
    patchParameterSpecialization t (A.residualHom P)
  exact congrArg (patchParameterSpecialization t) (DFunLike.congr_fun A.loweringHom_comp_top P)

noncomputable def loweringPoint (A : PolynomialSlots σ d w) (t : σ → ℝ) (b : Fin d → ℝ) :
    Fin d → ℝ := fun i => aeval b ((A.loweringAt t).val (X i))

theorem loweringAt_aeval (A : PolynomialSlots σ d w) (t : σ → ℝ) (b : Fin d → ℝ)
    (P : MvPolynomial (Fin d) ℝ) :
    aeval b ((A.loweringAt t).val P) = aeval (A.loweringPoint t b) P := by
  change aeval b ((A.loweringAt t).val.toAlgHom P) = _
  rw [MvPolynomial.aeval_unique (A.loweringAt t).val.toAlgHom, MvPolynomial.comp_aeval_apply]
  rfl

theorem top_factorization_coordinate (A : PolynomialSlots σ d w)
    (t : σ → ℝ) (b : Fin d → ℝ) (i : Fin d) :
    aeval (A.loweringPoint t b) (A.topResidualEquiv (X i)) =
      b i - (A.slots t).center b i := by
  have he := congrArg (fun F : MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ =>
    aeval b (F (X i))) (A.loweringAt_comp_top t)
  change aeval b ((A.loweringAt t).val (A.topResidualEquiv (X i))) =
    aeval b (patchParameterSpecialization t (A.residualHom (X i))) at he
  rw [A.loweringAt_aeval, patchParameterSpecialization_eval, residualHom_X,
    residualCoordinate_eval] at he
  exact he

theorem top_factorization_residual (A : PolynomialSlots σ d w)
    (t : σ → ℝ) (b : Fin d → ℤ) :
    (fun i => aeval (A.loweringPoint t (fun j => (b j : ℝ))) (A.topResidualEquiv (X i))) =
      (A.slots t).residual b := by
  funext i
  exact A.top_factorization_coordinate t (fun j => (b j : ℝ)) i

end PolynomialSlots

namespace PolynomialPatch

variable {s : ℕ}

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def symbolicShearHom (A : PolynomialSlots σ d w) :
    MvPolynomial (σ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (σ ⊕ Fin d) ℝ :=
  aeval (Sum.elim (fun a => X (Sum.inl a)) (fun i => A.loweringHom (X i)))

theorem symbolicShearHom_parameter (A : PolynomialSlots σ d w) (a : σ) :
    A.symbolicShearHom (X (Sum.inl a)) = X (Sum.inl a) := by
  simp only [symbolicShearHom, aeval_X, Sum.elim_inl]

theorem symbolicShearHom_slot (A : PolynomialSlots σ d w) (i : Fin d) :
    A.symbolicShearHom (X (Sum.inr i)) = A.loweringHom (X i) := by
  simp only [symbolicShearHom, aeval_X, Sum.elim_inr]

theorem symbolicShearHom_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n) :
    A.symbolicShearHom P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n := by
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro j
  cases j with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr i => exact A.loweringHom_degree (weightedSupportLE_X w i)

theorem symbolicShearHom_specialization (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (A.symbolicShearHom P) =
      A.loweringAtHom t (patchParameterSpecialization t P) := by
  have h : (patchParameterSpecialization t).comp A.symbolicShearHom =
      (A.loweringAtHom t).comp (patchParameterSpecialization t) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | inl a =>
      simp [AlgHom.comp_apply, symbolicShearHom_parameter, patchParameterSpecialization,
        loweringAtHom]
    | inr i =>
      change patchParameterSpecialization t (A.symbolicShearHom (X (Sum.inr i))) =
        A.loweringAtHom t (patchParameterSpecialization t (X (Sum.inr i)))
      rw [symbolicShearHom_slot, patchParameterSpecialization_X_slot]
      rfl
  exact DFunLike.congr_fun h P

theorem symbolicShearDifference_specialization (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (polynomialHomDifference A.symbolicShearHom P) =
      polynomialHomDifference (A.loweringAt t).val.toAlgHom (patchParameterSpecialization t P) := by
  change patchParameterSpecialization t (A.symbolicShearHom P - P) =
    A.loweringAtHom t (patchParameterSpecialization t P) - patchParameterSpecialization t P
  rw [map_sub, symbolicShearHom_specialization]

theorem symbolicShearDifference_pow_specialization (A : PolynomialSlots σ d w)
    (t : σ → ℝ) (k : ℕ) (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t ((polynomialHomDifference A.symbolicShearHom ^ k) P) =
      (polynomialHomDifference (A.loweringAt t).val.toAlgHom ^ k)
        (patchParameterSpecialization t P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, symbolicShearDifference_specialization, ih,
      pow_succ', Module.End.mul_apply]

theorem symbolicShearDifference_pow_degree (A : PolynomialSlots σ d w) (k : ℕ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n) :
    (polynomialHomDifference A.symbolicShearHom ^ k) P ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (weightedSupportLE _ n).sub_mem (A.symbolicShearHom_degree ih) ih

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R] [Algebra ℚ R]
variable {w₀ w₁ : σ → ℕ} {v₀ : τ → ℕ}

theorem polynomialShearExp_weightedSupportLE
    (D : PolynomialShearLieAlgebra w₀ R)
    (hD : ∀ i, D.val (X i) ∈ weightedSupportLE w₁ (w₁ i))
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w₁ n) :
    polynomialShearExp D P ∈ weightedSupportLE w₁ n := by
  have hP₀ : P ∈ weightedSupportLE w₀ (P.weightedTotalDegree w₀) :=
    (mem_weightedSupportLE_iff w₀ _ P).mpr le_rfl
  have hD₁ : ∀ i, D.val (X i) ∈ weightedSupportDrop w₁ (w₁ i) 0 := by
    simpa only [weightedSupportDrop_zero] using hD
  have hP₁ : P ∈ weightedSupportDrop w₁ n 0 := by
    simpa only [weightedSupportDrop_zero] using hP
  rw [polynomialShearExp_eq_sum D hP₀]
  apply ((weightedSupportLE (R := R) w₁ n).restrictScalars ℚ).sum_mem
  intro k hk
  apply ((weightedSupportLE (R := R) w₁ n).restrictScalars ℚ).smul_mem
  change (D.val.toLinearMap ^ k) P ∈ weightedSupportLE w₁ n
  simpa only [Nat.mul_zero, Nat.add_zero, weightedSupportDrop_zero] using
    weightedDerivation_pow w₁ D.val 0 hD₁ hP₁ k

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} {d : ℕ} (w : Fin d → ℕ)
variable [Fintype (PolynomialShearIndex w)]
variable (c : PolynomialShearIndex w → MvPolynomial σ ℝ)

noncomputable def polynomialSymbolicShearTerm (a : PolynomialShearIndex w) :
    MvPolynomial (σ ⊕ Fin d) ℝ :=
  rename Sum.inl (c a) * rename Sum.inr (monomial a.2.val 1)

theorem symbolic_rename_degree {ι κ : Type*} (v : ι → ℕ) (z : κ → ℕ)
    (f : ι → κ) (hf : ∀ i, z (f i) = v i)
    {P : MvPolynomial ι ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE v n) :
    rename f P ∈ weightedSupportLE z n := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval v z _ _ hP
  intro i
  simpa only [Function.comp_apply, hf] using weightedSupportLE_X (R := ℝ) z (f i)

omit [Fintype (PolynomialShearIndex w)] in
theorem polynomialSymbolicShearTerm_slot_degree (a : PolynomialShearIndex w) :
    polynomialSymbolicShearTerm w c a ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 0) w) (Finsupp.weight w a.2.val) := by
  have hp : c a ∈ weightedSupportLE (fun _ : σ => 0) 0 := by
    intro α hα
    simp [Finsupp.weight_apply, Finsupp.sum]
  have hc := symbolic_rename_degree (fun _ : σ => 0)
    (Sum.elim (fun _ : σ => 0) w) Sum.inl (fun _ => rfl) hp
  have hm := symbolic_rename_degree w (Sum.elim (fun _ : σ => 0) w)
    Sum.inr (fun _ => rfl) (weightedSupportLE_monomial w a.2.val (1 : ℝ))
  exact (by simpa only [zero_add, polynomialSymbolicShearTerm] using weightedSupportLE_mul hc hm)

omit [Fintype (PolynomialShearIndex w)] in
theorem polynomialSymbolicShearTerm_total_degree
    (hc : ∀ a, c a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a))
    (a : PolynomialShearIndex w) :
    polynomialSymbolicShearTerm w c a ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w a.1) := by
  have hp := symbolic_rename_degree (fun _ : σ => 1)
    (Sum.elim (fun _ : σ => 1) w) Sum.inl (fun _ => rfl) (hc a)
  have hm := symbolic_rename_degree w (Sum.elim (fun _ : σ => 1) w)
    Sum.inr (fun _ => rfl) (weightedSupportLE_monomial w a.2.val (1 : ℝ))
  apply weightedSupportLE_mono _ (weightedSupportLE_mul hp hm)
  have ha := a.2.property
  unfold polynomialShearDeficit
  omega

noncomputable def polynomialSymbolicShearSlot (i : Fin d) : MvPolynomial (σ ⊕ Fin d) ℝ :=
  ∑ a : PolynomialShearIndex w, if a.1 = i then polynomialSymbolicShearTerm w c a else 0

theorem polynomialSymbolicShearSlot_lower (i : Fin d) :
    polynomialSymbolicShearSlot w c i ∈
      weightedSupportDrop (Sum.elim (fun _ : σ => 0) w) (w i) 1 := by
  classical
  apply Submodule.sum_mem
  intro a ha
  split_ifs with hi
  · intro α hα
    have h := polynomialSymbolicShearTerm_slot_degree w c a hα
    change Finsupp.weight (Sum.elim (fun _ : σ => 0) w) α ≤ Finsupp.weight w a.2.val at h
    have hb := a.2.property
    change Finsupp.weight (Sum.elim (fun _ : σ => 0) w) α + 1 ≤ w i
    have hiw := congrArg w hi
    omega
  · exact Submodule.zero_mem _

noncomputable def polynomialSymbolicShearDerivation :
    PolynomialShearLieAlgebra (Sum.elim (fun _ : σ => 0) w) ℝ := by
  refine ⟨MvPolynomial.mkDerivation ℝ (Sum.elim (fun _ => 0) (polynomialSymbolicShearSlot w c)), ?_⟩
  intro i
  rw [MvPolynomial.mkDerivation_X]
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr i => exact polynomialSymbolicShearSlot_lower w c i

theorem polynomialSymbolicShearDerivation_X_parameter (i : σ) :
    (polynomialSymbolicShearDerivation w c).val (X (Sum.inl i)) = 0 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem polynomialSymbolicShearDerivation_X_slot (i : Fin d) :
    (polynomialSymbolicShearDerivation w c).val (X (Sum.inr i)) =
      polynomialSymbolicShearSlot w c i := MvPolynomial.mkDerivation_X _ _ _

theorem polynomialSymbolicShearDerivation_total_degree
    (hc : ∀ a, c a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a))
    (i : σ ⊕ Fin d) :
    (polynomialSymbolicShearDerivation w c).val (X i) ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (Sum.elim (fun _ : σ => 1) w i) := by
  classical
  cases i with
  | inl i => rw [polynomialSymbolicShearDerivation_X_parameter]; exact Submodule.zero_mem _
  | inr i =>
    rw [polynomialSymbolicShearDerivation_X_slot]
    apply Submodule.sum_mem
    intro a ha
    split_ifs with hi
    · simpa only [hi, Sum.elim_inr] using polynomialSymbolicShearTerm_total_degree w c hc a
    · exact Submodule.zero_mem _

theorem polynomialSymbolicShearExp_total_degree
    (hc : ∀ a, c a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a))
    {P : MvPolynomial (σ ⊕ Fin d) ℝ} {n : ℕ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n) :
    polynomialShearExp (polynomialSymbolicShearDerivation w c) P ∈
      weightedSupportLE (Sum.elim (fun _ : σ => 1) w) n :=
  polynomialShearExp_weightedSupportLE _ (polynomialSymbolicShearDerivation_total_degree w c hc) hP

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
variable {σ : Type*} {d : ℕ} (p : σ → ℕ) (w : Fin d → ℕ)
variable [Fintype (PolynomialShearIndex w)]
variable (c : PolynomialShearIndex w → MvPolynomial σ ℝ)

theorem weighted_symbolic_rename_degree {ι κ : Type*} (v : ι → ℕ) (z : κ → ℕ)
    (f : ι → κ) (hf : ∀ i, z (f i) = v i)
    {P : MvPolynomial ι ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE v n) :
    rename f P ∈ weightedSupportLE z n := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval v z _ _ hP
  intro i
  simpa only [Function.comp_apply, hf] using weightedSupportLE_X (R := ℝ) z (f i)

omit [Fintype (PolynomialShearIndex w)] in
theorem polynomialSymbolicShearTerm_weighted_degree
    (hc : ∀ a, c a ∈ weightedSupportLE p (polynomialShearDeficit w a))
    (a : PolynomialShearIndex w) :
    polynomialSymbolicShearTerm w c a ∈
      weightedSupportLE (Sum.elim p w) (w a.1) := by
  have hp := weighted_symbolic_rename_degree p
    (Sum.elim p w) Sum.inl (fun _ => rfl) (hc a)
  have hm := weighted_symbolic_rename_degree w (Sum.elim p w)
    Sum.inr (fun _ => rfl) (weightedSupportLE_monomial w a.2.val (1 : ℝ))
  apply weightedSupportLE_mono _ (weightedSupportLE_mul hp hm)
  have ha := a.2.property
  unfold polynomialShearDeficit
  omega

theorem polynomialSymbolicShearDerivation_weighted_degree
    (hc : ∀ a, c a ∈ weightedSupportLE p (polynomialShearDeficit w a))
    (i : σ ⊕ Fin d) :
    (polynomialSymbolicShearDerivation w c).val (X i) ∈
      weightedSupportLE (Sum.elim p w) (Sum.elim p w i) := by
  classical
  cases i with
  | inl i => rw [polynomialSymbolicShearDerivation_X_parameter]; exact Submodule.zero_mem _
  | inr i =>
    rw [polynomialSymbolicShearDerivation_X_slot]
    apply Submodule.sum_mem
    intro a ha
    split_ifs with hi
    · simpa only [hi, Sum.elim_inr] using polynomialSymbolicShearTerm_weighted_degree p w c hc a
    · exact Submodule.zero_mem _

theorem polynomialSymbolicShearExp_weighted_degree
    (hc : ∀ a, c a ∈ weightedSupportLE p (polynomialShearDeficit w a))
    {P : MvPolynomial (σ ⊕ Fin d) ℝ} {n : ℕ}
    (hP : P ∈ weightedSupportLE (Sum.elim p w) n) :
    polynomialShearExp (polynomialSymbolicShearDerivation w c) P ∈
      weightedSupportLE (Sum.elim p w) n :=
  polynomialShearExp_weightedSupportLE _ (polynomialSymbolicShearDerivation_weighted_degree p w c hc) hP

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearFactorialIntegrality
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

theorem WeightedLoweringAut.difference_pow_degree (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    (polynomialHomDifference e.val.toAlgHom ^ k) P ∈ weightedSupportLE w n := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact weightedSupportLT_le (e.difference_lower ih)

theorem WeightedLoweringAut.difference_pow_lower (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    (polynomialHomDifference e.val.toAlgHom ^ (k + 1)) P ∈ weightedSupportLT w n := by
  rw [pow_succ', Module.End.mul_apply]
  exact e.difference_lower (e.difference_pow_degree hP k)

variable [Algebra ℚ R]

noncomputable def polynomialShearLogOn (e : WeightedLoweringAut w R) (n : ℕ) :
    Module.End R (weightedSupportLE (R := R) w n) :=
  nilpotentLog ((e.degreeAction n).toLinearMap - 1)

theorem polynomialShearLogOn_sum (e : WeightedLoweringAut w R) (n : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    (polynomialShearLogOn e n P : MvPolynomial σ R) =
      ∑ k ∈ Finset.range (n + 1), ((-1 : ℚ) ^ (k + 1) / k) •
        (polynomialHomDifference e.val.toAlgHom ^ k) (P : MvPolynomial σ R) := by
  simp [polynomialShearLogOn,
    nilpotentLog_eq_sum (a := (e.degreeAction n).toLinearMap - 1)
      (e.degreeAction_difference_pow_zero n), e.degreeAction_difference_pow_coe]

theorem polynomialShearLogOn_mono (e : WeightedLoweringAut w R)
    {m n : ℕ} (hmn : m ≤ n) (P : weightedSupportLE (R := R) w m) :
    (polynomialShearLogOn e n ⟨P.val, weightedSupportLE_mono hmn P.property⟩ :
      MvPolynomial σ R) = (polynomialShearLogOn e m P : MvPolynomial σ R) := by
  let inc : weightedSupportLE (R := R) w m →ₗ[R] weightedSupportLE (R := R) w n :=
    Submodule.inclusion (fun _ h => weightedSupportLE_mono hmn h)
  have hc : ((e.degreeAction n).toLinearMap - 1) ∘ₗ inc =
      inc ∘ₗ ((e.degreeAction m).toLinearMap - 1) := by
    apply LinearMap.ext
    intro Q
    rfl
  have h := nilpotentLog_intertwine (e.degreeAction_difference_nilpotent m)
    (e.degreeAction_difference_nilpotent n) hc
  exact congrArg Subtype.val (LinearMap.congr_fun h P)

theorem polynomialShearLogOn_leibniz (e : WeightedLoweringAut w R) (m n : ℕ)
    (P : weightedSupportLE (R := R) w m) (Q : weightedSupportLE (R := R) w n) :
    (polynomialShearLogOn e (m + n) (weightedPolynomialMul w m n P Q) : MvPolynomial σ R) =
      (polynomialShearLogOn e m P : MvPolynomial σ R) * Q.val +
        P.val * (polynomialShearLogOn e n Q : MvPolynomial σ R) := by
  have h := nilpotentLog_bilinear (weightedPolynomialMul (R := R) w m n)
    (e.degreeAction m).toLinearMap (e.degreeAction n).toLinearMap
    (e.degreeAction (m + n)).toLinearMap
    (e.degreeAction_difference_nilpotent m) (e.degreeAction_difference_nilpotent n)
    (e.degreeAction_difference_nilpotent (m + n))
    (fun x y => Subtype.ext (map_mul e.val x.val y.val)) P Q
  exact congrArg Subtype.val h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def polynomialShearLogValue (e : WeightedLoweringAut w R)
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  polynomialShearLogOn e (P.weightedTotalDegree w)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩

theorem polynomialShearLogValue_eq_on (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearLogValue e P = (polynomialShearLogOn e n ⟨P, hP⟩ : MvPolynomial σ R) :=
  (polynomialShearLogOn_mono e ((mem_weightedSupportLE_iff w n P).mp hP)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩).symm

theorem polynomialShearLogValue_eq_sum (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearLogValue e P = ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℚ) ^ (k + 1) / k) • (polynomialHomDifference e.val.toAlgHom ^ k) P := by
  rw [polynomialShearLogValue_eq_on e hP]
  exact polynomialShearLogOn_sum e n ⟨P, hP⟩

theorem polynomialShearLogValue_add (e : WeightedLoweringAut w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearLogValue e (P + Q) = polynomialShearLogValue e P + polynomialShearLogValue e Q := by
  let n := P.weightedTotalDegree w + Q.weightedTotalDegree w
  have hp : P ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n P).mpr (Nat.le_add_right _ _)
  have hq : Q ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n Q).mpr (Nat.le_add_left _ _)
  rw [polynomialShearLogValue_eq_on e ((weightedSupportLE w n).add_mem hp hq),
    polynomialShearLogValue_eq_on e hp, polynomialShearLogValue_eq_on e hq]
  exact congrArg Subtype.val ((polynomialShearLogOn e n).map_add ⟨P, hp⟩ ⟨Q, hq⟩)

theorem polynomialShearLogValue_smul (e : WeightedLoweringAut w R)
    (c : R) (P : MvPolynomial σ R) :
    polynomialShearLogValue e (c • P) = c • polynomialShearLogValue e P := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearLogValue_eq_on e ((weightedSupportLE w _).smul_mem c hp),
    polynomialShearLogValue_eq_on e hp]
  exact congrArg Subtype.val ((polynomialShearLogOn e _).map_smul c ⟨P, hp⟩)

theorem polynomialShearLogValue_mul (e : WeightedLoweringAut w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearLogValue e (P * Q) =
      polynomialShearLogValue e P * Q + P * polynomialShearLogValue e Q := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  have hq : Q ∈ weightedSupportLE w (Q.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ Q).mpr le_rfl
  rw [polynomialShearLogValue_eq_on e (weightedSupportLE_mul hp hq),
    polynomialShearLogValue_eq_on e hp, polynomialShearLogValue_eq_on e hq]
  exact polynomialShearLogOn_leibniz e _ _ ⟨P, hp⟩ ⟨Q, hq⟩

theorem polynomialShearLogValue_C (e : WeightedLoweringAut w R) (c : R) :
    polynomialShearLogValue e (C c) = 0 := by
  rw [polynomialShearLogValue_eq_sum e (weightedSupportLE_C w 0 c)]
  simp

noncomputable def polynomialShearLogDerivation (e : WeightedLoweringAut w R) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) where
  toFun := polynomialShearLogValue e
  map_add' := polynomialShearLogValue_add e
  map_smul' := polynomialShearLogValue_smul e
  map_one_eq_zero' := by simpa using polynomialShearLogValue_C e 1
  leibniz' P Q := by
    change polynomialShearLogValue e (P * Q) =
      P • polynomialShearLogValue e Q + Q • polynomialShearLogValue e P
    rw [polynomialShearLogValue_mul]
    simp only [smul_eq_mul]
    ring

theorem polynomialShearLogValue_lower (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearLogValue e P ∈ weightedSupportLT w n := by
  rw [polynomialShearLogValue_eq_sum e hP, Finset.sum_range_succ']
  simp only [Nat.cast_zero, div_zero, zero_smul, add_zero]
  apply (weightedSupportLT w n).sum_mem
  intro k hk
  exact (weightedSupportLT (R := R) w n).restrictScalars ℚ |>.smul_mem _
    (e.difference_pow_lower hP k)

noncomputable def polynomialShearLog (e : WeightedLoweringAut w R) :
    PolynomialShearLieAlgebra w R :=
  ⟨polynomialShearLogDerivation e, fun i => by
    change polynomialShearLogValue e (X i) ∈ weightedSupportDrop w (w i) 1
    rw [weightedSupportDrop_one]
    exact polynomialShearLogValue_lower e (weightedSupportLE_X w i)⟩

theorem polynomialShearLog_apply (e : WeightedLoweringAut w R) (P : MvPolynomial σ R) :
    (polynomialShearLog e).val P = polynomialShearLogValue e P := rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearLog_end (e : WeightedLoweringAut w R) (n : ℕ) :
    polynomialShearEnd (polynomialShearLog e) n = polynomialShearLogOn e n := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact polynomialShearLogValue_eq_on e P.property

theorem polynomialShearExp_degreeAction (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    ((polynomialShearExpAut D).degreeAction n).toLinearMap = polynomialShearExpOn D n := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact polynomialShearExp_eq_on D P.property

theorem polynomialShearExp_log (e : WeightedLoweringAut w R) :
    polynomialShearExpAut (polynomialShearLog e) = e := by
  apply Subtype.ext
  apply DFunLike.ext
  intro P
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearExpAut_apply, polynomialShearExp_eq_on _ hp]
  unfold polynomialShearExpOn
  rw [polynomialShearLog_end, polynomialShearLogOn,
    exp_nilpotentLog (e.degreeAction_difference_nilpotent _)]
  simp [WeightedLoweringAut.degreeAction_apply_coe]

theorem polynomialShearLog_exp (D : PolynomialShearLieAlgebra w R) :
    polynomialShearLog (polynomialShearExpAut D) = D := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  change polynomialShearLogValue (polynomialShearExpAut D) (X i) = D.val (X i)
  rw [polynomialShearLogValue_eq_on _ (weightedSupportLE_X w i)]
  unfold polynomialShearLogOn
  rw [polynomialShearExp_degreeAction, polynomialShearExpOn,
    nilpotentLog_exp_sub_one (polynomialShearEnd_isNilpotent D (w i))]
  rfl

end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def symbolicLogSlot (A : PolynomialSlots σ d w) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin d) ℝ :=
  ∑ k ∈ Finset.range (w i + 1), ((-1 : ℚ) ^ (k + 1) / k) •
    (polynomialHomDifference A.symbolicShearHom ^ k) (X (Sum.inr i))

theorem symbolicLogSlot_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    A.symbolicLogSlot i ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w i) := by
  apply (weightedSupportLE _ _).sum_mem
  intro k hk
  exact (weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w i)).restrictScalars ℚ |>.smul_mem _
    (A.symbolicShearDifference_pow_degree k (weightedSupportLE_X _ (Sum.inr i)))

theorem symbolicLogSlot_specialization (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    patchParameterSpecialization t (A.symbolicLogSlot i) =
      (polynomialShearLog (A.loweringAt t)).val (X i) := by
  change patchParameterSpecialization t (A.symbolicLogSlot i) = polynomialShearLogValue (A.loweringAt t) (X i)
  rw [polynomialShearLogValue_eq_sum (A.loweringAt t) (weightedSupportLE_X w i)]
  unfold symbolicLogSlot
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_rat_smul, symbolicShearDifference_pow_specialization, patchParameterSpecialization_X_slot]

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem polynomialShear_scaled_pow (D : PolynomialShearLieAlgebra w ℚ)
    (c : ℚ) (k : ℕ) (P : MvPolynomial σ ℚ) :
    ((c • D).val.toLinearMap ^ k) P = c ^ k • (D.val.toLinearMap ^ k) P := by
  change ((c • D.val.toLinearMap) ^ k) P = _
  rw [smul_pow, LinearMap.smul_apply]

theorem polynomialShear_factorial_exp_integral (s : ℕ) (hw : ∀ i, w i ≤ s)
    (D : PolynomialShearLieAlgebra w ℚ)
    (hD : ∀ i, D.val (X i) ∈ integerCoefficientPolynomials σ) :
    polynomialShearExpAut ((s.factorial : ℚ) • D) ∈ integerWeightedLoweringSubgroup w := by
  intro i
  rw [polynomialShearExpAut_apply, polynomialShearExp_eq_sum _
    (weightedSupportLE_mono (hw i) (weightedSupportLE_X w i))]
  apply (integerCoefficientPolynomials σ).sum_mem
  intro k hk
  rw [polynomialShear_scaled_pow, smul_smul]
  exact integerCoefficientPolynomials_rat_smul
    (factorial_exp_scalar_integer s k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    (integerPolynomialDerivation_pow D.val hD (integerCoefficientPolynomials_X i) k)

theorem polynomialShear_factorial_log_integral (s : ℕ) (hw : ∀ i, w i ≤ s)
    (e : WeightedLoweringAut w ℚ) (he : e ∈ integerWeightedLoweringSubgroup w) (i : σ) :
    (s.factorial : ℚ) • (polynomialShearLog e).val (X i) ∈ integerCoefficientPolynomials σ := by
  rw [polynomialShearLog_apply, polynomialShearLogValue_eq_sum _
    (weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)), Finset.smul_sum]
  apply (integerCoefficientPolynomials σ).sum_mem
  intro k hk
  rw [smul_smul]
  exact integerCoefficientPolynomials_rat_smul
    (factorial_log_scalar_integer s k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    (integerWeightedLowering_difference_pow e he (integerCoefficientPolynomials_X i) k)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialEndomorphisms
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def weightedPolynomialEndDrop (w : σ → ℕ) (s k : ℕ) :
    Submodule R (Module.End R (weightedSupportLE (R := R) w s)) where
  carrier := {F | ∀ n r (P : weightedSupportLE (R := R) w s),
    (P : MvPolynomial σ R) ∈ weightedSupportDrop w n r →
      (F P : MvPolynomial σ R) ∈ weightedSupportDrop w n (r + k)}
  zero_mem' := fun n r _P _h => (weightedSupportDrop w n (r + k)).zero_mem
  add_mem' := fun hF hG n r P h => (weightedSupportDrop w n (r + k)).add_mem
    (hF n r P h) (hG n r P h)
  smul_mem' := fun c _F hF n r P h => (weightedSupportDrop w n (r + k)).smul_mem c
    (hF n r P h)

theorem weightedPolynomialEndDrop_antitone (w : σ → ℕ) (s : ℕ) :
    Antitone (weightedPolynomialEndDrop (R := R) w s) := by
  intro a b hab F hF n r P hP
  exact weightedSupportDrop_antitone (Nat.add_le_add_left hab r) (hF n r P hP)

theorem weightedPolynomialEndDrop_mul (w : σ → ℕ) (s a b : ℕ)
    {F G : Module.End R (weightedSupportLE (R := R) w s)}
    (hF : F ∈ weightedPolynomialEndDrop w s a) (hG : G ∈ weightedPolynomialEndDrop w s b) :
    F * G ∈ weightedPolynomialEndDrop w s (a + b) := by
  intro n r P hP
  have h := hF n (r + b) (G P) (hG n r P hP)
  change (F (G P) : MvPolynomial σ R) ∈ weightedSupportDrop w n (r + (a + b))
  simpa only [Nat.add_assoc, Nat.add_comm b a] using h

theorem weightedPolynomialEndDrop_one (w : σ → ℕ) (s : ℕ) :
    (1 : Module.End R (weightedSupportLE (R := R) w s)) ∈ weightedPolynomialEndDrop w s 0 := by
  intro n r P hP
  change (P : MvPolynomial σ R) ∈ weightedSupportDrop w n (r + 0)
  simpa only [Nat.add_zero] using hP

theorem weightedPolynomialEndDrop_terminal (w : σ → ℕ) (s : ℕ)
    {F : Module.End R (weightedSupportLE (R := R) w s)}
    (hF : F ∈ weightedPolynomialEndDrop w s (s + 1)) : F = 0 := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  have h := hF s 0 P (by simpa only [weightedSupportDrop_zero] using P.property)
  exact weightedSupportDrop_eq_zero (by omega) h

noncomputable def weightedPolynomialEndAlgebra (w : σ → ℕ) (s : ℕ) :
    Subalgebra R (Module.End R (weightedSupportLE (R := R) w s)) :=
  (weightedPolynomialEndDrop w s 0).toSubalgebra (weightedPolynomialEndDrop_one w s)
    (fun _ _ hF hG => weightedPolynomialEndDrop_mul w s 0 0 hF hG)

noncomputable instance weightedPolynomialEndAlgebraRing (w : σ → ℕ) (s : ℕ) :
    Ring (weightedPolynomialEndAlgebra (R := R) w s) :=
  @Subalgebra.toRing R (Module.End R (weightedSupportLE (R := R) w s)) _ _ _
    (weightedPolynomialEndAlgebra w s)

theorem polynomialShearEnd_mem_drop (w : σ → ℕ) (s k : ℕ)
    {D : PolynomialShearLieAlgebra w R} (hD : D ∈ polynomialShearLayer (R := R) w k) :
    polynomialShearEnd D s ∈ weightedPolynomialEndDrop w s k := by
  intro n r P hP
  exact weightedDerivation_apply w D.val k hD hP

noncomputable def weightedPolynomialEndLayer (w : σ → ℕ) (s k : ℕ) :
    Submodule ℚ (weightedPolynomialEndAlgebra (R := ℚ) w s) :=
  (weightedPolynomialEndDrop w s k).comap (weightedPolynomialEndAlgebra w s).val.toLinearMap

noncomputable def weightedPolynomialEndFiltration (w : σ → ℕ) (s : ℕ) :
    NilpotentAlgebraFiltration (weightedPolynomialEndAlgebra (R := ℚ) w s) s where
  layer := weightedPolynomialEndLayer w s
  antitone := by
    intro a b hab F hF
    exact weightedPolynomialEndDrop_antitone w s hab hF
  zero_eq_top := by
    apply top_unique
    intro F hF
    exact F.property
  mul_mem := by
    intro a b F G hF hG
    exact weightedPolynomialEndDrop_mul w s a b hF hG
  terminal := by
    apply bot_unique
    intro F hF
    change F = 0
    exact Subtype.ext (weightedPolynomialEndDrop_terminal w s hF)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialShearBCH
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ : Type*}

noncomputable def polynomialShearAssociativeAction (w : σ → ℕ) (s : ℕ) :
    PolynomialShearLieAlgebra w ℚ →ₗ⁅ℚ⁆ weightedPolynomialEndAlgebra (R := ℚ) w s where
  toLinearMap :=
    { toFun := fun D => ⟨polynomialShearEnd D s,
        weightedPolynomialEndDrop_antitone w s (Nat.zero_le 1)
          (polynomialShearEnd_mem_drop w s 1 D.property)⟩
      map_add' := by
        intro D E
        apply Subtype.ext
        exact (polynomialShearAction w s).map_add D E
      map_smul' := by
        intro c D
        apply Subtype.ext
        exact (polynomialShearAction w s).map_smul c D }
  map_lie' := by
    intro D E
    apply Subtype.ext
    exact (polynomialShearAction w s).map_lie D E

theorem polynomialShearAssociativeAction_positive (w : σ → ℕ) (s : ℕ)
    (D : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearAssociativeAction w s D ∈ (weightedPolynomialEndFiltration w s).layer 1 :=
  polynomialShearEnd_mem_drop w s 1 D.property

theorem polynomialShearExpOn_lieBCH (w : σ → ℕ) (s : ℕ)
    (D E : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearExpOn (lieBCH s D E) s = polynomialShearExpOn D s * polynomialShearExpOn E s := by
  let F := weightedPolynomialEndFiltration w s
  let φ := polynomialShearAssociativeAction w s
  have hp (A : PolynomialShearLieAlgebra w ℚ) : φ A ∈ F.layer 1 :=
    polynomialShearAssociativeAction_positive w s A
  have hnil (A : PolynomialShearLieAlgebra w ℚ) : IsNilpotent (φ A) :=
    F.isNilpotent_of_mem le_rfl (hp A)
  have he : IsNilpotent.exp (φ (lieBCH s D E)) = IsNilpotent.exp (φ D) * IsNilpotent.exp (φ E) := by
    rw [map_lieBCH, F.lieBCH_eq (hp D) (hp E)]
    exact exp_nilpotentBCH (F.layerAlgebra 1) F.positive_nilpotent (hp D) (hp E)
  have hv := congrArg (weightedPolynomialEndAlgebra (R := ℚ) w s).val he
  rw [map_mul, IsNilpotent.map_exp (hnil (lieBCH s D E)),
    IsNilpotent.map_exp (hnil D), IsNilpotent.map_exp (hnil E)] at hv
  exact hv

theorem polynomialShearExpAut_lieBCH (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (D E : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearExpAut (lieBCH s D E) = polynomialShearExpAut D * polynomialShearExpAut E := by
  apply WeightedLoweringAut.degreeActionHom_injective s hw
  apply LinearEquiv.toLinearMap_injective
  change ((polynomialShearExpAut (lieBCH s D E)).degreeAction s).toLinearMap =
    ((polynomialShearExpAut D).degreeAction s).toLinearMap *
      ((polynomialShearExpAut E).degreeAction s).toLinearMap
  rw [polynomialShearExp_degreeAction, polynomialShearExp_degreeAction,
    polynomialShearExp_degreeAction]
  exact polynomialShearExpOn_lieBCH w s D E

noncomputable def polynomialShearBCHEquiv (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).Group ≃* WeightedLoweringAut w ℚ where
  toFun A := polynomialShearExpAut A.coord
  invFun e := ⟨polynomialShearLog e⟩
  left_inv A := NilpotentLieBCHGroup.ext (polynomialShearLog_exp A.coord)
  right_inv := polynomialShearExp_log
  map_mul' A B := polynomialShearExpAut_lieBCH w s hw A.coord B.coord

end Erdos3

end

end OAI

end


