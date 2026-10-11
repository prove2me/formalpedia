-- Prove2me | Definitions.Def_OAIErdos3B203
-- name    : OAIErdos3B203
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T14:24:44.411984+00:00
-- url     : https://prove2.me/theorems/c9febf80-8b28-45e2-b53f-a4a963211611
-- title:
--   OpenAI Erdős-3 split, definitions bundle 204 of 207
-- statement:
--   Definitions bundle 204 of 207 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B202`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 204 available.
--
--   Modules: `OAI.Erdos3.CyclicNativeInverse`, `OAI.Erdos3.MixedNonconstantCorner`, `OAI.Erdos3.NativeCommonDerivativeModels`, `OAI.Erdos3.NativeCommonDerivativeModels.mono`, `OAI.Erdos3.NativeCyclicModel.noConfusion`, `OAI.Erdos3.NativeCyclicModel.smul`, `OAI.Erdos3.NativeIntegerExpansion.boxCornerPullback`, `OAI.Erdos3.NativeIntegerExpansion.conjugationPower`, `OAI.Erdos3.NativeIntegerExpansion.exists_division_expansion`, `OAI.Erdos3.NativeIntegerExpansion.raiseStep`, `OAI.Erdos3.NativeModelDetector`, `OAI.Erdos3.NativeMultidegreeNilcharacter.dilationTensorMixedExchangeCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.divisionMixedExchangeCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.divisionMixedExchangeCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.divisionMixedExchangeCorrection_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.divisionMixedExchangeCorrection_pointwise_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.division_dilation_integer_representative`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_divisionMixedExchangeCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_division_mixed_last_slots_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_division_mixed_tensor_last_slots_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixedDiagonalWrapCoefficient_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixedRootCornerCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixedRootExchangeCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixedTensorExchangeCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_anchor_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_antisymmetric_family`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_corner_exchange_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_corner_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_corner_product_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_diagonal_derivative_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_diagonal_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_frozen_affine_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_integration_root_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_kernel_coordinate_slice`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_permuted_diagonal_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_rational_division_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_reflected_factor_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_reflected_pair_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_reflection_weights`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_root_last_slots_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_scalar_coordinate_slice`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_sum_antisymmetric_box`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_sum_antisymmetric_correlation`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_sum_kernel_correlation`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_original_mixed_root_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_sampled_rational_division_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedAntisymmetric`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCanonicalTensor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCanonicalTensor_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCornerExchangeFactor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCornerExchangeFactor_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCornerExchangeFactor_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCornerExchangeProduct`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCornerExchangeProduct_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCyclicDiagonalDerivative`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCyclicDiagonalDerivative_branches`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCyclicDiagonalDerivative_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCyclicDiagonalDerivative_unit`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedDiagonalDerivative`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedDiagonalDerivative_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedDiagonalTensor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedDiagonalWrapCoefficient`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedDiagonalWrapCoefficient_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedIntegrationRoot`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedIntegrationRoot_outputDim`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedNonconstantTensor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedNonconstantTensor_cross_symmetric`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedNonconstantTensor_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedNonconstantTensor_unit`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPairComponent`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPairComponent_complexity`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPairComponent_eval`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPairComponent_vertical`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPermutedDiagonalCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPermutedDiagonalCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRawCornerFactor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRawCornerFactor_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedReflectionSource`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedReflectionTarget`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRootCornerCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRootCornerCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRootCornerCorrection_mean_error_power`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRootExchangeCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRootExchangeCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRootExchangeCorrection_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedTensorExchangeCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedTensorExchangeCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedTensorExchangeCorrection_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedTensorExchange_kernel`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedWrappedDiagonalDerivative`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedWrappedDiagonalDerivative_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedWrappedDiagonalDerivative_resolution`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixed_reflection_target_unit`, `OAI.Erdos3.NativeSampleCorrelation.MixedPairAlgebra`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairBudget_six_le`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairFrequencies`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairModels`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairTests`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairTests_complexity`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairTests_eval`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairTests_vertical`, `OAI.Erdos3.NativeTwoSiteModelingData`, `OAI.Erdos3.NativeVerticalDerivativeData.mono`, `OAI.Erdos3.NativeVerticalDerivativeData.recOn`, `OAI.Erdos3.PositiveShiftBasis.CommonFactorization`, `OAI.Erdos3.PositiveShiftBasis.CommonFactorization.FactorFamily`, `OAI.Erdos3.PositiveShiftBasis.CommonFactorization.mono`, `OAI.Erdos3.PositiveShiftBasis.CommonRefilteredExpansionSpec`, `OAI.Erdos3.PositiveShiftBasis.productExpansionBudget`, `OAI.Erdos3.card_pairResidue_le_exp`, `OAI.Erdos3.complexCrossContraction`, `OAI.Erdos3.complexCrossContraction_rank_one`, `OAI.Erdos3.complexCrossContraction_unit`, `OAI.Erdos3.cyclicNativeInverse_one`, `OAI.Erdos3.divisionPolynomial`, `OAI.Erdos3.divisionPolynomial_eval`, `OAI.Erdos3.divisionPolynomial_support`, `OAI.Erdos3.exists_cyclicSecondDifference_approximation_degree`, `OAI.Erdos3.exists_mixed_kernel_correlation`, `OAI.Erdos3.exists_native_cross_contraction`, `OAI.Erdos3.exists_normalized_native_common_models`, `OAI.Erdos3.exists_pairResidueIndicator_expansion`, `OAI.Erdos3.exists_quadratic_small_modulus_correlation`, `OAI.Erdos3.exists_separated_family_correlation`, `OAI.Erdos3.exists_smoothedSecondDifference_expansion_degree`, `OAI.Erdos3.expect_mixed_tuple`, `OAI.Erdos3.mean_complexCrossContraction_error_le_card`, `OAI.Erdos3.mean_norm_le_fourier_sum`, `OAI.Erdos3.mem_mixedAllCoordinates`, `OAI.Erdos3.mixedAllCoordinates`, `OAI.Erdos3.mixedAllCoordinates_get`, `OAI.Erdos3.mixedAllCoordinates_length`, `OAI.Erdos3.mixedAllCoordinates_nodup`, `OAI.Erdos3.mixedCanonicalSample`, `OAI.Erdos3.mixedCanonicalSample_eq_sorted`, `OAI.Erdos3.mixedCanonicalSample_of_first_one`, `OAI.Erdos3.mixedCanonicalSample_of_first_zero`, `OAI.Erdos3.mixedCoordinateIndex`, `OAI.Erdos3.mixedCoordinateIndex_coordinate`, `OAI.Erdos3.mixedCornerAssignmentEquiv`, `OAI.Erdos3.mixedCornerCount`, `OAI.Erdos3.mixedCornerSample`, `OAI.Erdos3.mixedCornerSample_input`, `OAI.Erdos3.mixedCornerSample_zeroCount`, `OAI.Erdos3.mixedCornerWeight`, `OAI.Erdos3.mixedCorner_exists_tail_one`, `OAI.Erdos3.mixedDiagonalChoiceInput`, `OAI.Erdos3.mixedDiagonalChoice_leaf`, `OAI.Erdos3.mixedDiagonalChoice_sum`, `OAI.Erdos3.mixedDiagonalCorner`, `OAI.Erdos3.mixedDiagonalCorner_zero`, `OAI.Erdos3.mixedExchangeCoordinate`, `OAI.Erdos3.mixedExchangeCoordinate_involutive`, `OAI.Erdos3.mixedExchangeCoordinate_update`, `OAI.Erdos3.mixedExchangePermutation`, `OAI.Erdos3.mixedHeadIndex`, `OAI.Erdos3.mixedHeadIndex_one`, `OAI.Erdos3.mixedHeadPermutation`, `OAI.Erdos3.mixedInputCoordinate`, `OAI.Erdos3.mixedInputCoordinate_eval`, `OAI.Erdos3.mixedInputCoordinate_index`, `OAI.Erdos3.mixedNonconstantCorner_card`, `OAI.Erdos3.mixedNonconstantCorner_card_eq`, `OAI.Erdos3.mixedPairBudget`, `OAI.Erdos3.mixedPermuteSample`, `OAI.Erdos3.mixedPermuteSample_eq_comp`, `OAI.Erdos3.mixedPostExchangePermutation`, `OAI.Erdos3.mixedPreExchangeSample`, `OAI.Erdos3.mixedPreExchangeSample_one`, `OAI.Erdos3.mixedReflectionAffineInput`, `OAI.Erdos3.mixedReflectionAffineInput_none`, `OAI.Erdos3.mixedReflectionAffineInput_some`, `OAI.Erdos3.mixedReflectionInput_left`, `OAI.Erdos3.mixedReflectionInput_right`, `OAI.Erdos3.mixedReflectionInput_sum`, `OAI.Erdos3.mixedReflectionLinear`, `OAI.Erdos3.mixedReflectionOffset`, `OAI.Erdos3.mixedReplicated_totalDegree`, `OAI.Erdos3.mixedRootCornerCoefficient`, `OAI.Erdos3.mixedRootCornerExponent`, `OAI.Erdos3.mixedRootTensorExponent`, `OAI.Erdos3.mixedSampledInput`, `OAI.Erdos3.mixedSampledInput_coordinates`, `OAI.Erdos3.mixedSampledInput_slots`, `OAI.Erdos3.mixedSlotInput`, `OAI.Erdos3.mixedSlotInput_update`, `OAI.Erdos3.mixedSwapSample`, `OAI.Erdos3.mixedSwapSample_input`, `OAI.Erdos3.mixedTailSortPermutation`, `OAI.Erdos3.nativeCyclicFunctions`, `OAI.Erdos3.norm_complexCrossContraction_le_card`, `OAI.Erdos3.norm_sub_complexCrossContraction_le_sum`, `OAI.Erdos3.pairResidueIndicator`, `OAI.Erdos3.pairResidueIndicator_product`, `OAI.Erdos3.root_corner_loss_identity`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B063

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
namespace OAI

section

namespace Erdos3

def mixedSlotInput {n : ℕ} {α : Type*} (h t : α) (v : Fin n → α) :
    MixedReplicatedIndex (n + 1) → α := mixedReplicatedInput h (Fin.cons t v)

theorem mixedSlotInput_update {n : ℕ} {α : Type*} (h t u : α) (v : Fin n → α) :
    Function.update (mixedSlotInput h t v) (mixedReplica 0) u = mixedSlotInput h u v := by
  classical
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · have hne : mixedHead (n + 1) ≠ mixedReplica (0 : Fin (n + 1)) := by
      intro heq
      have hf := congrArg (fun a : MixedReplicatedIndex (n + 1) => a.1) heq
      norm_num [mixedHead, mixedReplica] at hf
    simp only [Function.update_of_ne hne, mixedSlotInput, mixedReplicatedInput_head]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Function.update_self, mixedSlotInput, mixedReplicatedInput_replica, Fin.cons_zero]
    · have hne : mixedReplica i.succ ≠ mixedReplica (0 : Fin (n + 1)) :=
        fun heq => Fin.succ_ne_zero i (mixedReplica_injective (n + 1) heq)
      simp only [Function.update_of_ne hne, mixedSlotInput, mixedReplicatedInput_replica, Fin.cons_succ]

def mixedExchangeCoordinate (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))

def mixedReflectionLinear (n : ℕ) (j : Option (MixedReplicatedIndex (n + 1))) :
    (Fin (n + 2) → ℤ) →+ ℤ :=
  let ev (i : Fin (n + 2)) : (Fin (n + 2) → ℤ) →+ ℤ :=
    ⟨⟨fun x => x i, rfl⟩, fun _ _ => rfl⟩
  match j with
  | none => ev 1
  | some a => mixedSlotInput (ev 0) (-ev 0 - ev 1) (fun i => ev i.succ.succ) a

def mixedReflectionOffset (n : ℕ) (c : ℤ) : Option (MixedReplicatedIndex (n + 1)) → ℤ
  | none => 0
  | some j => mixedSlotInput 0 c (fun _ : Fin n => 0) j

def mixedReflectionAffineInput (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ)
    (j : Option (MixedReplicatedIndex (n + 1))) : ℤ :=
  mixedReflectionOffset n c j + mixedReflectionLinear n j x

theorem mixedReflectionAffineInput_none (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    mixedReflectionAffineInput n c x none = x 1 := by
  simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear]

theorem mixedReflectionAffineInput_some (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ)
    (j : MixedReplicatedIndex (n + 1)) :
    mixedReflectionAffineInput n c x (some j) =
      mixedSlotInput (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) j := by
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear,
      mixedSlotInput, mixedReplicatedInput_head]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear,
        mixedSlotInput, mixedReplicatedInput_replica, sub_eq_add_neg, add_assoc]
    · simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear,
        mixedSlotInput, mixedReplicatedInput_replica]

theorem mixedReflectionInput_sum (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    coordinateAdditionInputs (mixedReplica 0) (mixedReflectionAffineInput n c x) 0 =
      mixedSlotInput (x 0) (c - x 0) (fun i => x i.succ.succ) := by
  rw [coordinateAdditionInputs_sum]
  simp only [mixedReflectionAffineInput_some, mixedReflectionAffineInput_none]
  rw [show mixedSlotInput (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) (mixedReplica 0) =
    c - x 0 - x 1 from rfl, sub_add_cancel, mixedSlotInput_update]

theorem mixedReflectionInput_left (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    coordinateAdditionInputs (mixedReplica 0) (mixedReflectionAffineInput n c x) 1 =
      mixedSlotInput (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) := by
  funext j
  exact mixedReflectionAffineInput_some n c x j

theorem mixedReflectionInput_right (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    coordinateAdditionInputs (mixedReplica 0) (mixedReflectionAffineInput n c x) 2 =
      mixedSlotInput (x 0) (x 1) (fun i => x i.succ.succ) := by
  rw [coordinateAdditionInputs_right]
  simp only [mixedReflectionAffineInput_some, mixedReflectionAffineInput_none, mixedSlotInput_update]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def mixedReflectionSource {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (a : Fin W.outputDim × Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  W.eval a.1 (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
    star (W.eval a.2 (mixedSlotInput (x 1) (c - x 0 - x 1) (fun j => x j.succ.succ)))

noncomputable def mixedReflectionTarget {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim))
    (x : Fin (n + 2) → ℤ) : ℂ :=
  W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
    star (W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ))) *
    star (W.eval a.1.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))) *
    W.eval a.2.2 (mixedSlotInput (x 1) (x 0) (fun j => x j.succ.succ))

theorem exists_mixed_reflected_factor_equivalence (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p) (c : ℤ),
      NativeIntegerVectorEquivalence (n + 1) ((p + C) ^ C)
        (fun i (x : Fin (n + 2) → ℤ) => W.eval i
          (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)))
        (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval a.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
            star (W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ)))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence
    (fun _ : MixedReplicatedIndex (n + 1) => 1)
  refine ⟨C, hC, ?_⟩
  intro p W c
  have hdegree : (∑ _ : MixedReplicatedIndex (n + 1), 1) - 1 = n + 1 := by
    have hc : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 := replicatedMixed_card (n + 1)
    simp only [Finset.sum_const, Finset.card_univ, hc, smul_eq_mul, mul_one]
    omega
  have E := (hadd W (mixedReplica 0) rfl).affinePullbackHom
    (mixedReflectionLinear n) (mixedReflectionOffset n c)
  have hinput (x : Fin (n + 2) → ℤ) :
      (fun j => mixedReflectionOffset n c j + mixedReflectionLinear n j x) =
        mixedReflectionAffineInput n c x := rfl
  have E' : NativeIntegerVectorEquivalence (n + 1) ((p + C) ^ C)
      (fun i (x : Fin (n + 2) → ℤ) => W.eval i
        (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)))
      (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval a.1 (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
          W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))) := by
    simpa only [hdegree, coordinateSumVector, coordinateTensorVector,
      hinput, mixedReflectionInput_sum,
      mixedReflectionInput_left, mixedReflectionInput_right] using E
  refine ⟨E'.left_dimension, E'.right_dimension, ?_⟩
  intro i a
  obtain ⟨R⟩ := E'.symm.expansion (i, a.2) a.1
  have heq :
      (fun x : Fin (n + 2) → ℤ =>
        (W.eval i (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
          W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))) *
            star (W.eval a.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)))) =
      (fun x => W.eval i (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
        star (W.eval a.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
          star (W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))))) := by
    funext x
    simp only [star_mul, star_star]
    ring
  exact ⟨heq ▸ R⟩

theorem exists_mixed_reflected_pair_equivalence (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p) (c : ℤ),
      NativeIntegerVectorEquivalence (n + 1) ((p + C) ^ C)
        (W.mixedReflectionSource c) (W.mixedReflectionTarget c) := by
  obtain ⟨a, _, hfactor⟩ := exists_mixed_reflected_factor_equivalence n
  obtain ⟨b, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have E := hfactor W c
  have F := (E.coordinatePullback (mixedExchangeCoordinate n)).conjugate
  have R := htensor hq E F
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have h0 : mixedExchangeCoordinate n 0 = 1 := rfl
  have h1 : mixedExchangeCoordinate n 1 = 0 := rfl
  have ht (i : Fin n) : mixedExchangeCoordinate n i.succ.succ = i.succ.succ := rfl
  have hsub (x : Fin (n + 2) → ℤ) : c - x 1 - x 0 = c - x 0 - x 1 := by abel
  unfold mixedReflectionSource mixedReflectionTarget
  simpa only [h0, h1, ht, hsub, star_mul, star_star, mul_assoc, mul_comm, mul_left_comm]
    using R.mono hcost

theorem mixed_reflection_target_unit {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (x : Fin (n + 2) → ℤ) :
    ∑ a, ‖W.mixedReflectionTarget c a x‖ ^ 2 = 1 := by
  have heq (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim)) :
      W.mixedReflectionTarget c a x =
        (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
          star (W.eval a.1.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ)))) *
        star (W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ)) *
          star (W.eval a.2.2 (mixedSlotInput (x 1) (x 0) (fun j => x j.succ.succ)))) := by
    simp only [mixedReflectionTarget, star_mul, star_star]
    ring
  simp only [heq, norm_mul, norm_star, mul_pow, Fintype.sum_prod_type,
    ← Finset.mul_sum, W.unit_eval, mul_one]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_separated_family_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ {J K : Type*} [Fintype J] [Fintype K]
        {chi : J → (Fin (s + 1) → ℤ) → ℂ} {eta : K → (Fin (s + 1) → ℤ) → ℂ},
      NativeIntegerVectorEquivalence s p chi eta →
      (∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) →
      ∀ {G Ω : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset Ω), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → Ω → Fin (s + 1) → ℤ) (f : G → Ω → ℂ),
      (∀ h ∈ H, ∀ u ∈ S h, ‖f h u‖ ≤ 1) →
      ∀ (j : J) (A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
      (∀ i x, ‖A i x‖ ≤ 1) →
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → A i x = A i y) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 u ∈ S h, f h u * star (chi j (sample h u)) * ∏ i, A i (sample h u)‖) →
      ∃ (k : K) (B : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
        (∀ i x, ‖B i x‖ ≤ 1) ∧
        (∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 u ∈ S h, f h u * star (eta k (sample h u)) * ∏ i, B i (sample h u)‖ := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_missing_coordinate_error s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * X + (3 * X + 2 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p hp J K _ _ chi eta E hunit G Ω H hH S hS sample f hf j A hA hAind hcorr
  classical
  let P := Σ k : K, Fin (E.selectedExpansion j k).count
  let rel (h : G) (_ : Unit) (c : P) : Prop :=
    Real.exp (-(p + 2 * p)) ≤ ‖𝔼 u ∈ S h,
      (f h u * ∏ i, A i (sample h u)) * star (eta c.1 (sample h u)) *
        star (((E.selectedExpansion j c.1).test c.2).eval (sample h u))‖
  have hchoice : ∀ h ∈ H, ∀ u, ∃ c, rel h u c := by
    intro h hh _
    obtain ⟨k, l, hl⟩ := E.transfer_sample_correlation (S h) (sample h) j
      (fun u => f h u * ∏ i, A i (sample h u)) (fun u _ => hunit (sample h u)) (by
        simpa only [mul_right_comm] using hcorr h hh)
    exact ⟨⟨k, l⟩, hl⟩
  have hcount : (Fintype.card P : ℝ) ≤ Real.exp (2 * p) := by
    change (Fintype.card (Σ k : K, Fin (E.selectedExpansion j k).count) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _k : K, Real.exp p := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [Fintype.card_fin] using (E.selectedExpansion j k).count_bound
      _ = (Fintype.card K : ℝ) * Real.exp p := by simp
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul_of_nonneg_right E.right_dimension (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, two_mul]
  obtain ⟨c, H₁, hsub₁, hH₁, hsize₁, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice hcount
  have hsize₁' : Real.exp (-(2 * p)) * (H.card : ℝ) ≤ (H₁.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize₁
  let T := (E.selectedExpansion j (c ()).1).test (c ()).2
  let r := 3 * p + 2
  let t := (r + a) ^ a
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have h3pr : p + 2 * p ≤ r := by dsimp only [r]; linarith
  have htotal : 2 * p + t ≤ (p + C) ^ C := by
    simpa [X, r, t, Polynomial.eval₂_pow] using hbudget p hp
  have htc : t ≤ (p + C) ^ C := by linarith
  have heta (x : Fin (s + 1) → ℤ) : ‖eta (c ()).1 x‖ ≤ 1 := by
    have hle : ‖eta (c ()).1 x‖ ^ 2 ≤ ∑ k, ‖eta k x‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖eta k x‖) (Finset.mem_univ _)
    rw [hunit] at hle
    nlinarith only [hle, norm_nonneg (eta (c ()).1 x)]
  let F (h : G) (u : Ω) := f h u * star (eta (c ()).1 (sample h u)) * ∏ i, A i (sample h u)
  have hF : ∀ h ∈ H₁, ∀ u ∈ S h, ‖F h u‖ ≤ 1 := by
    intro h hh u hu
    dsimp only [F]
    rw [norm_mul, norm_mul, norm_star, norm_prod]
    exact (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      ((mul_le_of_le_one_left (norm_nonneg _) (hf h (hsub₁ hh) u hu)).trans (heta _))).trans
      (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hA i _))
  have hFcorr : ∀ h ∈ H₁, Real.exp (-r) ≤
      ‖𝔼 u ∈ S h, F h u * star (T.eval (sample h u))‖ := by
    intro h hh
    have ht := hfixed h hh ()
    dsimp only [rel] at ht
    simpa only [F, T, mul_right_comm] using
      (Real.exp_le_exp.mpr (neg_le_neg h3pr)).trans ht
  obtain ⟨D, hD, hDind, H₂, hsub₂, hH₂, hsize₂, hfinal⟩ := habsorb T
    (((E.selectedExpansion j (c ()).1).complexity (c ()).2).mono hpr)
    H₁ hH₁ S (fun h hh => hS h (hsub₁ hh)) sample F hF hFcorr
  refine ⟨(c ()).1, (fun i x => A i x * D i x), ?_, ?_, H₂, hsub₂.trans hsub₁, hH₂, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hD i x)
  · intro i x y hxy
    change A i x * D i x = A i y * D i y
    rw [hAind i x y hxy, hDind i x y hxy]
  · calc
      _ ≤ Real.exp (-(2 * p + t)) * (H.card : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (Nat.cast_nonneg _)
      _ = Real.exp (-t) * (Real.exp (-(2 * p)) * (H.card : ℝ)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-t) * (H₁.card : ℝ) :=
        mul_le_mul_of_nonneg_left hsize₁' (Real.exp_nonneg _)
      _ ≤ _ := hsize₂
  · intro h hh
    simpa only [F, Finset.prod_mul_distrib, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg htc)).trans (hfinal h hh)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def mixedAntisymmetric {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (a b : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  W.eval a (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ)) *
    star (W.eval b (mixedSlotInput (x 1) (x 0) (fun j => x j.succ.succ)))

theorem exists_mixed_reflection_weights {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim))
    (B : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ)
    (hB : ∀ i x, ‖B i x‖ ≤ 1)
    (hBind : ∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) :
    ∃ C : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ,
      (∀ i x, ‖C i x‖ ≤ 1) ∧
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → C i x = C i y) ∧
      ∀ x, star (W.mixedReflectionTarget c a x) * (∏ i, B i x) =
        W.mixedAntisymmetric a.1.2 a.2.2 x * ∏ i, C i x := by
  classical
  let F (i : Fin 2) (x : Fin (n + 2) → ℤ) : ℂ :=
    Fin.cases
      (W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ)))
      (fun _ => star (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)))) i
  have hF0 (x : Fin (n + 2) → ℤ) : F 0 x =
      W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ)) := rfl
  have hF1 (x : Fin (n + 2) → ℤ) : F 1 x =
      star (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ))) := rfl
  have hF : ∀ i x, ‖F i x‖ ≤ 1 := by
    intro i x
    fin_cases i
    · exact W.norm_eval _ _
    · change ‖F 1 x‖ ≤ 1
      simpa only [hF1, norm_star] using W.norm_eval a.1.1
        (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ))
  have hFind : ∀ i, ∃ k : Fin (n + 2), ∀ x y,
      (∀ l, l ≠ k → x l = y l) → F i x = F i y := by
    intro i
    fin_cases i
    · refine ⟨0, ?_⟩
      intro x y hxy
      have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
        funext (fun j => hxy j.succ.succ (Fin.succ_ne_zero j.succ))
      change W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) _) =
        W.eval a.2.1 (mixedSlotInput (y 1) (c - y 1) _)
      rw [hxy 1 (Fin.succ_ne_zero (0 : Fin (n + 1))), ht]
    · refine ⟨1, ?_⟩
      intro x y hxy
      have hne (j : Fin n) : j.succ.succ ≠ (1 : Fin (n + 2)) := by
        intro heq
        exact Fin.succ_ne_zero j (Fin.succ_injective (n + 1) heq)
      have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
        funext (fun j => hxy j.succ.succ (hne j))
      change star (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) _)) =
        star (W.eval a.1.1 (mixedSlotInput (y 0) (c - y 0) _))
      rw [hxy 0 (Fin.succ_ne_zero (0 : Fin (n + 1))).symm, ht]
  obtain ⟨D, hD, hDind, hDprod⟩ := exists_missing_coordinate_product_factors F hF hFind
  refine ⟨(fun i x => B i x * D i x), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hB i x)).trans (hD i x)
  · intro i x y hxy
    change B i x * D i x = B i y * D i y
    rw [hBind i x y hxy, hDind i x y hxy]
  · intro x
    rw [Finset.prod_mul_distrib, hDprod]
    simp only [Fin.prod_univ_two, hF0, hF1,
      mixedReflectionTarget, mixedAntisymmetric, star_mul, star_star]
    ring

theorem exists_mixed_antisymmetric_family (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (c : ℤ) (i j : Fin W.outputDim),
      ∀ {G Ω : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset Ω), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → Ω → Fin (n + 2) → ℤ) (f : G → Ω → ℂ),
      (∀ h ∈ H, ∀ u ∈ S h, ‖f h u‖ ≤ 1) →
      ∀ (A : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
      (∀ k x, ‖A k x‖ ≤ 1) →
      (∀ k x y, (∀ l, l ≠ k → x l = y l) → A k x = A k y) →
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 u ∈ S h,
        f h u * star (W.mixedReflectionSource c (i, j) (sample h u)) * ∏ k, A k (sample h u)‖) →
      ∃ (i' j' : Fin W.outputDim) (B : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
        (∀ k x, ‖B k x‖ ≤ 1) ∧
        (∀ k x y, (∀ l, l ≠ k → x l = y l) → B k x = B k y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 u ∈ S h, f h u * W.mixedAntisymmetric i' j' (sample h u) * ∏ k, B k (sample h u)‖ := by
  obtain ⟨a, _, hreflect⟩ := exists_mixed_reflected_pair_equivalence n
  obtain ⟨b, _, htransfer⟩ := exists_separated_family_correlation (n + 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Q + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W c i j G Ω H hH S hS sample f hf A hA hAind hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have E := hreflect W c
  obtain ⟨k, B, hB, hBind, H', hsub, hH', hsize, hBcorr⟩ := htransfer hr (E.mono hqr)
    (W.mixed_reflection_target_unit c) H hH S hS sample f hf (i, j) A hA hAind
    (fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hcorr h hh))
  obtain ⟨D, hD, hDind, hpoint⟩ := W.exists_mixed_reflection_weights c k B hB hBind
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨k.1.2, k.2.2, D, hD, hDind, H', hsub, hH', ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg _)).trans hsize
  · intro h hh
    have heq : (𝔼 u ∈ S h, f h u * star (W.mixedReflectionTarget c k (sample h u)) *
        ∏ l, B l (sample h u)) =
        𝔼 u ∈ S h, f h u * W.mixedAntisymmetric k.1.2 k.2.2 (sample h u) * ∏ l, D l (sample h u) := by
      apply Finset.expect_congr rfl
      intro u _
      rw [mul_assoc, hpoint, ← mul_assoc]
    rw [← heq]
    exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hBcorr h hh)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators Classical

theorem exists_mixed_sum_antisymmetric_correlation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ (j k : Fin W.outputDim) (B : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
        (∀ j x, ‖B j x‖ ≤ 1) ∧
        (∀ j x y, (∀ l, l ≠ j → x l = y l) → B j x = B j y) ∧
        Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 u : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
            W.mixedAntisymmetric j k
                (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun l => (u l).val))) *
              ∏ l, B l (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun j => (u j).val)))‖ := by
  obtain ⟨b, _, htransfer⟩ := exists_mixed_antisymmetric_family n
  let X : Polynomial ℕ := Polynomial.X
  let R := X + Polynomial.C (2 * 2 ^ (n + 1)) * X + 12
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := 2 * ((2 ^ (n + 1) : ℕ) : ℝ) * p + 10
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  let K (_ : Unit) (h m : ℤ) (u : Fin n → ℤ) := star (W.eval i (mixedSlotInput h m u))
  have hK : ∀ t h m u, ‖K t h m u‖ ≤ 1 := by
    intro t h m u
    simpa only [K, norm_star] using W.norm_eval i (mixedSlotInput h m u)
  obtain ⟨z, carry, D, hD, hDind, hreflect⟩ := exists_cyclic_mixed_reflection n hp K hK
    (fun _ => f) (fun _ => hf) (fun _ => A) (fun _ => hA) (fun _ => hmiss) (by
      simpa only [K, Fintype.expect_const] using hcorr)
  let c : ℤ := z.val + (carry.val : ℤ) * N
  let V := W.mono hpr
  let sample (t : (Fin n → ZMod N) × (ZMod N × ZMod N)) : Fin (n + 2) → ℤ :=
    Fin.cons (t.2.1.val : ℤ) (Fin.cons (t.2.2.val : ℤ) (fun l => (t.1 l).val))
  have hpoint (u : Fin n → ZMod N) (h h' : ZMod N) :
      star (V.mixedReflectionSource c (i, i) (sample (u, (h, h')))) =
        K () h.val (c - h.val - h'.val) (fun l => (u l).val) *
          star (K () h'.val (c - h.val - h'.val) (fun l => (u l).val)) := by
    change star (W.eval i (mixedSlotInput (h.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val)) *
      star (W.eval i (mixedSlotInput (h'.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val)))) =
        star (W.eval i (mixedSlotInput (h.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val))) *
          star (star (W.eval i (mixedSlotInput (h'.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val))))
    simp only [star_mul, star_star]
    exact mul_comm _ _
  have hsource : Real.exp (-r) ≤
      ‖𝔼 t : (Fin n → ZMod N) × (ZMod N × ZMod N),
        star (V.mixedReflectionSource c (i, i) (sample t)) * ∏ l, D () l (sample t)‖ := by
    simp_rw [expect_prod_split, hpoint]
    simpa only [Fintype.univ_unit, Finset.expect_singleton, sample, c] using
      (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans hreflect
  obtain ⟨j, k, B, hB, hBind, H, _, hH, _, hfinal⟩ := htransfer V c i i
    (Finset.univ : Finset Unit) Finset.univ_nonempty
    (fun _ => (Finset.univ : Finset ((Fin n → ZMod N) × (ZMod N × ZMod N))))
    (fun _ _ => Finset.univ_nonempty) (fun _ => sample) (fun _ _ => (1 : ℂ))
    (fun _ _ _ _ => by norm_num) (D ()) (hD ()) (hDind ())
    (fun _ _ => by simpa only [one_mul] using hsource)
  obtain ⟨t, ht⟩ := hH
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    convert hbudget p hp using 1
    simp [X, R, r, q, Polynomial.eval₂_pow, Nat.cast_mul]
    ring
  have hmono (x : Fin (n + 2) → ℤ) :
      V.mixedAntisymmetric j k x = W.mixedAntisymmetric j k x := rfl
  simp_rw [hmono] at hfinal
  refine ⟨j, k, B, hB, hBind, ?_⟩
  simpa only [expect_prod_split, sample, one_mul] using
    (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hfinal t ht)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeMixedCoordinateSlices
namespace OAI

section

namespace Erdos3

def mixedInputCoordinate (n : ℕ) : MixedReplicatedIndex (n + 1) → Fin (n + 2) :=
  mixedSlotInput 0 1 (fun j => j.succ.succ)

def mixedCoordinateIndex (n : ℕ) : Fin (n + 2) → MixedReplicatedIndex (n + 1) :=
  Fin.cases (mixedHead (n + 1)) (fun j => mixedReplica j)

theorem mixedInputCoordinate_index (n : ℕ) (k : Fin (n + 2)) :
    mixedInputCoordinate n (mixedCoordinateIndex n k) = k := by
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

theorem mixedInputCoordinate_eval (n : ℕ) {α : Type*} (x : Fin (n + 2) → α) :
    (fun j => x (mixedInputCoordinate n j)) =
      mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨k, rfl⟩
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

theorem mixedExchangeCoordinate_involutive (n : ℕ) :
    Function.Involutive (mixedExchangeCoordinate n) := by
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

theorem mixedExchangeCoordinate_update (n : ℕ) {α : Type*}
    (x : Fin (n + 2) → α) (d : Fin (n + 2)) (c : α) :
    Function.update (fun k => x (mixedExchangeCoordinate n k)) (mixedExchangeCoordinate n d) c =
      fun k => (Function.update x d c) (mixedExchangeCoordinate n k) := by
  funext k
  have hi (k : Fin (n + 2)) :
      mixedExchangeCoordinate n (mixedExchangeCoordinate n k) = k :=
    mixedExchangeCoordinate_involutive n k
  by_cases h : k = mixedExchangeCoordinate n d
  · subst k
    simp only [Function.update_self, hi]
  · have hk : mixedExchangeCoordinate n k ≠ d := by
      intro heq
      apply h
      have h' := congrArg (mixedExchangeCoordinate n) heq
      simpa only [hi] using h'
    simp only [Function.update_of_ne h, Function.update_of_ne hk]

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_mixed_frozen_affine_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : (MixedReplicatedIndex (n + 1)) => 1) p)
      (d : (MixedReplicatedIndex (n + 1))) (A : (MixedReplicatedIndex (n + 1)) → Fin (n + 2) → ℤ)
      (b : (MixedReplicatedIndex (n + 1)) → ℤ) (out : Fin W.outputDim),
      (∀ k, A d k = 0) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => W.eval out (integerAffineMap A b x))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_freezing_niltest (fun _ : (MixedReplicatedIndex (n + 1)) => 1)
  refine ⟨C, hC, ?_⟩
  intro p W d A b out hA
  classical
  let S : Finset (MixedReplicatedIndex (n + 1)) := Finset.univ.erase d
  have hcard : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 :=
    replicatedMixed_card (n + 1)
  have hdegree : (∑ j ∈ S, (1 : ℕ)) = n + 1 := by simp [S, hcard]
  obtain ⟨t, dim, ht, _hdim, D, hD⟩ := hfreeze W S b out
  have ht3 : t = n + 1 := ht.trans hdegree
  rcases ht3 with rfl
  let K := W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 D.basis
  obtain ⟨T, _hTnorm, hT, _hzero, heval⟩ := hD
  let U := T.affinePullback (fun j k => A j.val k) (fun j => b j.val)
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hvalue (x : Fin (n + 2) → ℤ) : U.eval x = W.eval out (integerAffineMap A b x) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, heval]
    apply congrArg (W.eval out)
    funext j
    by_cases hj : j ∈ S
    · simp [freezeCoordinates, hj, integerAffineMap]
    · have hjd : j = d := by simpa [S] using hj
      subst j
      simp [freezeCoordinates, hj, integerAffineMap, hA]
  let E : NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C) U.eval :=
    NativeIntegerExpansion.ofTest U hU (fun _ => rfl)
  have heq : U.eval = (fun x => W.eval out (integerAffineMap A b x)) := funext hvalue
  exact ⟨heq ▸ E⟩

theorem exists_mixed_scalar_coordinate_slice (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (out : Fin W.outputDim) (d : Fin (n + 2)) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => let z := Function.update x d c
          W.eval out (mixedSlotInput (z 0) (z 1) (fun l => z l.succ.succ)))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_mixed_frozen_affine_expansion n
  refine ⟨C, hC, ?_⟩
  intro p W out d c
  let coord := mixedInputCoordinate n
  let index := mixedCoordinateIndex n
  have hindex (k : Fin (n + 2)) : coord (index k) = k := mixedInputCoordinate_index n k
  let A : MixedReplicatedIndex (n + 1) → Fin (n + 2) → ℤ := fun j k =>
    if coord j = d then 0 else if k = coord j then 1 else 0
  let b : MixedReplicatedIndex (n + 1) → ℤ := fun j => if coord j = d then c else 0
  obtain ⟨E⟩ := hfreeze W (index d) A b out (by intro k; simp [A, hindex])
  have hmap (x : Fin (n + 2) → ℤ) (j : MixedReplicatedIndex (n + 1)) :
      integerAffineMap A b x j = (Function.update x d c) (coord j) := by
    by_cases hj : coord j = d <;> simp [integerAffineMap, A, b, hj, ite_mul]
  have heq (x : Fin (n + 2) → ℤ) : integerAffineMap A b x =
      mixedSlotInput ((Function.update x d c) 0) ((Function.update x d c) 1)
        (fun l => (Function.update x d c) l.succ.succ) := by
    funext j
    rw [hmap]
    exact congrFun (mixedInputCoordinate_eval n (Function.update x d c)) j
  exact ⟨by simpa only [heq] using E⟩

theorem exists_mixed_kernel_coordinate_slice (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (i j : Fin W.outputDim) (d : Fin (n + 2)) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => W.mixedAntisymmetric i j (Function.update x d c))) := by
  obtain ⟨A, _, hscalar⟩ := exists_mixed_scalar_coordinate_slice n
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j d c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let e := mixedExchangeCoordinate n
  have he0 : e 0 = 1 := rfl
  have he1 : e 1 = 0 := rfl
  have hetail (l : Fin n) : e l.succ.succ = l.succ.succ := rfl
  have hswap (x : Fin (n + 2) → ℤ) : Function.update (fun k => x (e k)) (e d) c =
      fun k => (Function.update x d c) (e k) := mixedExchangeCoordinate_update n x d c
  obtain ⟨L⟩ := hscalar W i d c
  obtain ⟨R⟩ := hscalar W j (e d) c
  have R' : NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) q
      (fun x => let z := Function.update x d c
        W.eval j (mixedSlotInput (z 1) (z 0) (fun l => z l.succ.succ))) := by
    have E : NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) q
        (fun x => let z := Function.update (fun k => x (e k)) (e d) c
          W.eval j (mixedSlotInput (z 0) (z 1) (fun l => z l.succ.succ))) :=
      R.linearPullbackHom (fun k => ⟨⟨fun x => x (e k), rfl⟩, fun _ _ => rfl⟩)
    simpa only [hswap, he0, he1, hetail] using E
  obtain ⟨F⟩ := hmul hq L R'.conjugate
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedAnchorExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def NativeIntegerExpansion.boxCornerPullback {n s : ℕ} {p : ℝ}
    {F : (Fin n → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : Fin n => 1) s p F)
    (a : Fin n → ℤ) (ω : Fin n → Bool) :
    NativeIntegerExpansion (fun _ : Fin n => 1) s p (fun x => F (boxCorner x a ω)) := by
  let A : Fin n → Fin n → ℤ := fun i j => if ω i then 0 else if j = i then 1 else 0
  let b : Fin n → ℤ := fun i => if ω i then a i else 0
  have hmap (x : Fin n → ℤ) : integerAffineMap A b x = boxCorner x a ω := by
    funext i
    cases h : ω i <;> simp [integerAffineMap, A, b, boxCorner, h, ite_mul]
  simpa only [hmap] using E.affinePullback A b

noncomputable def NativeIntegerExpansion.conjugationPower {σ : Type*} {w : σ → ℕ}
    {s : ℕ} {p : ℝ} {F : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p F) (n : ℕ) :
    NativeIntegerExpansion w s p (fun x => Erdos3.conjugationPower n (F x)) := by
  by_cases h : n % 2 = 0
  · simpa only [conjugationPower_eq_if_mod, h, ite_true] using E
  · simpa only [conjugationPower_eq_if_mod, h, ite_false] using E.conjugate

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem NativeMultidegreeNilcharacter.exists_mixed_corner_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (i j : Fin W.outputDim) (a : Fin (n + 2) → ℤ) (ω : Fin (n + 2) → Bool),
      ω ≠ (fun _ => false) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => W.mixedAntisymmetric i j (boxCorner x a ω))) := by
  obtain ⟨C, hC, hslice⟩ := NativeMultidegreeNilcharacter.exists_mixed_kernel_coordinate_slice n
  refine ⟨C, hC, ?_⟩
  intro p W i j a ω hω
  obtain ⟨k, hk⟩ := exists_true_of_ne_false hω
  obtain ⟨E⟩ := hslice W i j k (a k)
  have hupdate (x : Fin (n + 2) → ℤ) :
      Function.update (boxCorner x a ω) k (a k) = boxCorner x a ω := by
    funext l
    by_cases h : l = k
    · subst l
      simp [boxCorner, hk]
    · simp [h]
  exact ⟨by simpa only [hupdate] using E.boxCornerPullback a ω⟩

theorem NativeMultidegreeNilcharacter.exists_mixed_anchor_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (i j : Fin W.outputDim) (a : Fin (n + 2) → ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (boxCornerAnchor (W.mixedAntisymmetric i j) a)) := by
  obtain ⟨A, _, hcorner⟩ := NativeMultidegreeNilcharacter.exists_mixed_corner_expansion n
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget (2 ^ (n + 2) - 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j a
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let S : Finset (Fin (n + 2) → Bool) := Finset.univ.erase (fun _ => false)
  have hS : Fintype.card S = 2 ^ (n + 2) - 1 := by simp [S]
  let e : Fin (2 ^ (n + 2) - 1) ≃ S := (Fintype.equivFinOfCardEq hS).symm
  let f : Fin (2 ^ (n + 2) - 1) → (Fin (n + 2) → ℤ) → ℂ := fun l x =>
    conjugationPower (booleanWeight (e l).val)
      (W.mixedAntisymmetric i j (boxCorner x a (e l).val))
  have hf (l : Fin (2 ^ (n + 2) - 1)) : Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) q (f l)) := by
    have hne : (e l).val ≠ (fun _ => false) := (Finset.mem_erase.mp (e l).property).1
    obtain ⟨E⟩ := hcorner W i j a (e l).val hne
    exact ⟨E.conjugationPower (booleanWeight (e l).val)⟩
  obtain ⟨E⟩ := hprod f hq hf
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have heq (x : Fin (n + 2) → ℤ) : (∏ l, f l x) = boxCornerAnchor (W.mixedAntisymmetric i j) a x := by
    exact boxCornerAnchor_prod_equiv e (W.mixedAntisymmetric i j) a x
  exact ⟨by simpa only [heq] using E.mono hcost⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositiveDegreeCyclicDifference
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def raiseStep {σ : Type*} {w : σ → ℕ} {s t : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p f) (hst : s ≤ t) (hp : 0 ≤ p) :
    NativeIntegerExpansion w t (raisedNiltestBudget p) f :=
  { E with
    count_bound := E.count_bound.trans (Real.exp_le_exp.mpr (le_raisedNiltestBudget p))
    model := fun i => (E.model i).raiseStep hst
    test := fun i => (E.test i).raiseStep hst
    complexity := fun i => (E.test i).raiseStep_complexity hst hp (E.complexity i)
    cost := E.cost.trans (Real.exp_le_exp.mpr (le_raisedNiltestBudget p))
    eval := fun x => by
      simpa only [RationalFilteredNilmanifold.Niltest.raiseStep_eval] using E.eval x }

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_smoothedSecondDifference_expansion_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      ∀ (N : ℕ) (δ : ℝ≥0), 0 < δ → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p (integerSecondDifference u v k)) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p (integerSecondDifference u v (k - N))) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + e + C) ^ C)
        (smoothedSecondDifference N δ u v k)) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 6) ^ 2 + 7
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + Polynomial.C A) ^ A + R + 2)
  refine ⟨C, hC, ?_⟩
  intro p e hp he N δ hδ hinv u v k ⟨E0⟩ ⟨E1⟩
  let r := p + e + (p + e + 6) ^ 2 + 7
  let t := (r + A) ^ A + r
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + e + 6)]
  have her : raisedNiltestBudget (e + 4) ≤ r := by
    have hsq : (e + 6) ^ 2 ≤ (p + e + 6) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    dsimp [raisedNiltestBudget, r]
    nlinarith
  have hrt : r ≤ t := le_add_of_nonneg_left (by positivity)
  have hmt : (r + A) ^ A ≤ t := le_add_of_nonneg_right hr
  have htC : t + 2 ≤ (p + e + C) ^ C := by
    simpa [X, R, r, t, Polynomial.eval₂_pow] using hbudget (p + e) (by linarith)
  obtain ⟨EC⟩ := exists_fixed_shift_smoothCyclicCarry_expansion N δ hδ he hinv k
  obtain ⟨EM0⟩ := hmul hr ((EC.raiseStep hs (by linarith)).mono her) (E0.mono hpr)
  obtain ⟨EM1⟩ := hmul hr ((EC.raiseStep hs (by linarith)).mono her) (E1.mono hpr)
  let w (x : Fin 2 → ℤ) := (smoothCyclicCarry N δ ![k, x 1] : ℂ)
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![integerSecondDifference u v k,
    (fun x => w x * integerSecondDifference u v (k - N) x),
    (fun x => w x * integerSecondDifference u v k x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s t (fs j)) := by
    fin_cases j
    · exact ⟨E0.mono (hpr.trans hrt)⟩
    · exact ⟨EM1.mono hmt⟩
    · exact ⟨EM0.mono hmt⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono htC
  have heq : (fun x => ∑ j, cs j * fs j x) = smoothedSecondDifference N δ u v k := by
    funext x
    simp [cs, fs, w, Fin.sum_univ_succ, smoothedSecondDifference]
    ring
  exact ⟨heq ▸ E⟩

theorem exists_cyclicSecondDifference_approximation_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (u v : (Fin 2 → ℤ) → ℂ), (∀ x, ‖u x‖ ≤ 1) → (∀ x, ‖v x‖ ≤ 1) →
      (∀ k : ℤ, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p
        (integerSecondDifference u v k))) →
      ∀ k : ZMod N, ∃ K : (Fin 2 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + e + C) ^ C) K) ∧
        ∀ h : ℤ, (𝔼 n : ZMod N,
          ‖cyclicSecondDifference u v k h n - K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hexpand⟩ := exists_smoothedSecondDifference_expansion_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 16 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p e hp he N _ hN u v hu hv hmodel k
  let δ : ℝ≥0 := ⟨Real.exp (-(e + 16)), (Real.exp_pos _).le⟩
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp (e + 16) := by
    change (Real.exp (-(e + 16)))⁻¹ ≤ Real.exp (e + 16)
    rw [← Real.exp_neg, neg_neg]
  have hbudget' : (p + (e + 16) + A) ^ A ≤ (p + e + C) ^ C := by
    have hb := hbudget (p + e) (by linarith)
    simpa [X, Polynomial.eval₂_pow, add_assoc] using hb
  obtain ⟨E⟩ := hexpand hp (by linarith : 0 ≤ e + 16) N δ hδ hinv u v k.val
    (hmodel k.val) (hmodel ((k.val : ℤ) - N))
  refine ⟨smoothedSecondDifference N δ u v k.val, ⟨E.mono hbudget'⟩, ?_⟩
  intro h
  apply (smoothedSecondDifference_mean_error δ hδ u v hu hv k h).trans
  have hNinv : 1 / (N : ℝ) ≤ Real.exp (-(e + 16)) := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (e + 16)) hN
    simpa only [one_div, ← Real.exp_neg] using hh
  have htwo : 2 / (N : ℝ) ≤ 2 * Real.exp (-(e + 16)) := by
    calc
      _ = 2 * (1 / (N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNinv (by norm_num)
  calc
    12 * (δ : ℝ) + 2 / N ≤ 14 * Real.exp (-(e + 16)) := by
      change 12 * Real.exp (-(e + 16)) + 2 / (N : ℝ) ≤ 14 * Real.exp (-(e + 16))
      linarith only [htwo]
    _ ≤ Real.exp 16 * Real.exp (-(e + 16)) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (16 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (-e) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerDivision
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def divisionPolynomial {σ : Type*} (d : ℕ) (r : σ → ℤ) (i : σ) : MvPolynomial σ ℚ :=
  MvPolynomial.C (d : ℚ)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (r i : ℚ))

theorem divisionPolynomial_support {σ : Type*} (d : ℕ) (r : σ → ℤ) (i : σ) :
    divisionPolynomial d r i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  have hx : (MvPolynomial.X i : MvPolynomial σ ℚ) ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : σ => 1) (Finsupp.single i 1) (1 : ℚ)
  simpa only [divisionPolynomial, zero_add] using
    weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 (d : ℚ)⁻¹)
      (Submodule.sub_mem _ hx (weightedSupportLE_C _ 1 (r i : ℚ)))

theorem divisionPolynomial_eval {σ : Type*} (d : ℕ) [NeZero d] (r x : σ → ℤ)
    (hr : ∀ i, x i % (d : ℤ) = r i) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (divisionPolynomial d r i) =
      ((x i / (d : ℤ) : ℤ) : ℚ) := by
  have hi : x i = (d : ℤ) * (x i / (d : ℤ)) + r i := by
    calc
      _ = x i % (d : ℤ) + (d : ℤ) * (x i / (d : ℤ)) := (Int.emod_add_mul_ediv _ _).symm
      _ = _ := by rw [hr i]; ring
  have hiq : (x i : ℚ) = (d : ℚ) * ((x i / (d : ℤ) : ℤ) : ℚ) + (r i : ℚ) := by
    exact_mod_cast hi
  simp only [divisionPolynomial, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  change (d : ℚ)⁻¹ * ((x i : ℚ) - (r i : ℚ)) = ((x i / (d : ℤ) : ℤ) : ℚ)
  rw [hiq, add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d)), one_mul]

noncomputable def pairResidueIndicator {d : ℕ} (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) : ℂ :=
  if (fun i => (x i : ZMod d)) = r then 1 else 0

theorem pairResidueIndicator_product {d : ℕ} (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) :
    pairResidueIndicator r x =
      (if (x 0 : ZMod d) = r 0 then 1 else 0) *
        (if (x 1 : ZMod d) = r 1 then 1 else 0) := by
  classical
  have heq : (fun i => (x i : ZMod d)) = r ↔ (x 0 : ZMod d) = r 0 ∧ (x 1 : ZMod d) = r 1 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> assumption
  unfold pairResidueIndicator
  simp only [heq]
  split_ifs <;> simp_all

theorem exists_pairResidueIndicator_expansion (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ r : Fin 2 → ZMod d,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s (C : ℝ) (pairResidueIndicator r)) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let D := d + 2 + (d + 4) ^ 2 + 3
  refine ⟨(D + A) ^ A + 2, by omega, ?_⟩
  intro r
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  obtain ⟨E0⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 0 (r 0) (Nat.cast_nonneg d) hd
  obtain ⟨E1⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 1 (r 1) (Nat.cast_nonneg d) hd
  have hraise : raisedNiltestBudget ((d : ℝ) + 2) = (D : ℝ) := by
    dsimp [D, raisedNiltestBudget]
    push_cast
    ring
  have F0 : NativeIntegerExpansion (fun _ : Fin 2 => 1) s D
      (fun x => if (x 0 : ZMod d) = r 0 then 1 else 0) := by
    simpa only [hraise] using E0.raiseStep hs (by positivity)
  have F1 : NativeIntegerExpansion (fun _ : Fin 2 => 1) s D
      (fun x => if (x 1 : ZMod d) = r 1 then 1 else 0) := by
    simpa only [hraise] using E1.raiseStep hs (by positivity)
  obtain ⟨F⟩ := hmul (Nat.cast_nonneg D) F0 F1
  have hb : ((D : ℝ) + A) ^ A ≤ (((D + A) ^ A + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  have heq : (fun x => (if (x 0 : ZMod d) = r 0 then (1 : ℂ) else 0) *
      (if (x 1 : ZMod d) = r 1 then 1 else 0)) = pairResidueIndicator r := by
    funext x
    exact (pairResidueIndicator_product r x).symm
  rw [heq] at F
  exact ⟨F.mono hb⟩

theorem card_pairResidue_le_exp (d : ℕ) [NeZero d] :
    (Fintype.card (Fin 2 → ZMod d) : ℝ) ≤ Real.exp ((d : ℝ) ^ 2) := by
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow]
  linarith [Real.add_one_le_exp ((d : ℝ) ^ 2)]

theorem NativeIntegerExpansion.exists_division_expansion (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} {f : (Fin 2 → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion (fun _ : Fin 2 => 1) s p f →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + C) ^ C)
        (fun x => f (fun i => x i / (d : ℤ)))) := by
  obtain ⟨A, _, hresidue⟩ := exists_pairResidueIndicator_expansion d s hs
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A + 2 + Polynomial.C B) ^ B + Polynomial.C (d ^ 2))
  refine ⟨C, hC, ?_⟩
  intro p f hp E
  classical
  let t : ℝ := p + A + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) A; linarith
  have hAt : (A : ℝ) ≤ t := by dsimp [t]; linarith
  let P (r : Fin 2 → ZMod d) := divisionPolynomial d (fun i => ((r i).val : ℤ))
  have hP (r : Fin 2 → ZMod d) (i : Fin 2) :
      P r i ∈ weightedSupportLE (fun _ : Fin 2 => 1) 1 := divisionPolynomial_support d _ i
  let F (r : Fin 2 → ZMod d) := E.substitutedValue (P r) (hP r)
  have hF (r : Fin 2 → ZMod d) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s
      ((t + B) ^ B) (fun x => pairResidueIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hAt)
      ((E.substituteExpansion (P r) (hP r)).mono hpt)
  have hcost : (∑ _ : Fin 2 → ZMod d, ‖(1 : ℂ)‖) ≤ Real.exp ((d : ℝ) ^ 2) := by
    simpa using card_pairResidue_le_exp d
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hF r)) (fun _ => 1)
    (sq_nonneg (d : ℝ)) (card_pairResidue_le_exp d) hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod d, (1 : ℂ) * (pairResidueIndicator r x * F r x)) =
      (fun x => f (fun i => x i / (d : ℤ))) := by
    funext x
    let r : Fin 2 → ZMod d := fun i => (x i : ZMod d)
    rw [Finset.sum_eq_single r]
    · simp only [pairResidueIndicator, r, ite_true, one_mul]
      apply E.substitutedValue_eq (P r) (hP r) x (fun i => x i / (d : ℤ))
      exact divisionPolynomial_eval d _ x (fun i => (ZMod.val_intCast (x i)).symm)
    · intro a _ ha
      have hne : (fun i => (x i : ZMod d)) ≠ a := fun h => ha h.symm
      simp only [pairResidueIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  have hb : (t + B) ^ B + (d : ℝ) ^ 2 ≤ (p + C) ^ C := by
    simpa [t, X, Polynomial.eval₂_pow] using hbudget p hp
  rw [heq] at S
  exact ⟨S.mono hb⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuarticRootExchange
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def complexCrossContraction {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ) : ℂ :=
  ∑ kl : K × L, (a * star (u kl.1)) * star (b * star (v kl.2)) * G kl.1 kl.2

theorem complexCrossContraction_rank_one {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u f : K → ℂ) (v g : L → ℂ) :
    complexCrossContraction a b u v (fun k l => f k * star (g l)) =
      (a * star b) * (∑ k, star (u k) * f k) * star (∑ l, star (v l) * g l) := by
  simp only [complexCrossContraction, Fintype.sum_prod_type, star_sum,
    star_mul, star_star, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem complexCrossContraction_unit {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ l, ‖v l‖ ^ 2 = 1) :
    complexCrossContraction a b u v (fun k l => u k * star (v l)) = a * star b := by
  rw [complexCrossContraction_rank_one]
  have hU : ∑ k, star (u k) * u k = (1 : ℂ) := by
    simpa only [one_mul] using (complex_unit_vector_resolution u hu 1).symm
  have hV : ∑ l, star (v l) * v l = (1 : ℂ) := by
    simpa only [one_mul] using (complex_unit_vector_resolution v hv 1).symm
  rw [hU, hV, star_one, mul_one, mul_one]

theorem norm_sub_complexCrossContraction_le_sum {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ l, ‖v l‖ ^ 2 = 1)
    (hucap : ∀ k, ‖u k‖ ≤ 1) (hvcap : ∀ l, ‖v l‖ ≤ 1) :
    ‖a * star b - complexCrossContraction a b u v G‖ ≤
      ∑ kl : K × L, ‖u kl.1 * star (v kl.2) - G kl.1 kl.2‖ := by
  have hid : a * star b - complexCrossContraction a b u v G =
      ∑ kl : K × L, ((a * star (u kl.1)) * star (b * star (v kl.2))) *
        (u kl.1 * star (v kl.2) - G kl.1 kl.2) := by
    rw [← complexCrossContraction_unit a b u v hu hv]
    simp only [complexCrossContraction, mul_sub, Finset.sum_sub_distrib]
  rw [hid]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro kl _
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_mul, norm_star, norm_star, norm_mul, norm_star]
  refine (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
  · exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hucap kl.1)
  · exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hvcap kl.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_complexCrossContraction_le_card {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ) {B : ℝ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ∀ k, ‖u k‖ ≤ 1) (hv : ∀ l, ‖v l‖ ≤ 1) (hG : ∀ k l, ‖G k l‖ ≤ B) :
    ‖complexCrossContraction a b u v G‖ ≤ (Fintype.card (K × L) : ℝ) * B := by
  unfold complexCrossContraction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : K × L, B := by
      apply Finset.sum_le_sum
      intro kl _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hG kl.1 kl.2)
      rw [norm_mul, norm_star, norm_mul, norm_star, norm_mul, norm_star]
      refine (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
      · exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hu kl.1)
      · exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hv kl.2)
    _ = _ := by simp

theorem mean_complexCrossContraction_error_le_card {K L X : Type*}
    [Fintype K] [Fintype L] [Fintype X]
    (a b : X → ℂ) (u : K → X → ℂ) (v : L → X → ℂ) (G : K → L → X → ℂ) {ε : ℝ}
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ x, ‖b x‖ ≤ 1)
    (hu : ∀ x, ∑ k, ‖u k x‖ ^ 2 = 1) (hv : ∀ x, ∑ l, ‖v l x‖ ^ 2 = 1)
    (hucap : ∀ k x, ‖u k x‖ ≤ 1) (hvcap : ∀ l x, ‖v l x‖ ≤ 1)
    (herr : ∀ k l, (𝔼 x, ‖u k x * star (v l x) - G k l x‖) ≤ ε) :
    (𝔼 x, ‖a x * star (b x) - complexCrossContraction (a x) (b x)
      (fun k => u k x) (fun l => v l x) (fun k l => G k l x)‖) ≤
      (Fintype.card (K × L) : ℝ) * ε := by
  calc
    _ ≤ 𝔼 x, ∑ kl : K × L, ‖u kl.1 x * star (v kl.2 x) - G kl.1 kl.2 x‖ := by
      apply Finset.expect_le_expect
      intro x _
      exact norm_sub_complexCrossContraction_le_sum (a x) (b x)
        (fun k => u k x) (fun l => v l x) (fun k l => G k l x)
        (ha x) (hb x) (hu x) (hv x) (fun k => hucap k x) (fun l => hvcap l x)
    _ = ∑ kl : K × L, 𝔼 x, ‖u kl.1 x * star (v kl.2 x) - G kl.1 kl.2 x‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : K × L, ε := Finset.sum_le_sum (fun kl _ => herr kl.1 kl.2)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_cross_contraction :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K L M : Type*}
      [Fintype J] [Fintype K] [Fintype L] [Fintype M] {s : ℕ} {p : ℝ}
      {a : J → (σ → ℤ) → ℂ} {u : K → (σ → ℤ) → ℂ}
      {b : L → (σ → ℤ) → ℂ} {v : M → (σ → ℤ) → ℂ}
      (G : K → M → (σ → ℤ) → ℂ),
      0 ≤ p → NativeIntegerVectorEquivalence s p a u → NativeIntegerVectorEquivalence s p b v →
      (∀ k m, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p (G k m))) →
      ∀ j l, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
        (fun x => complexCrossContraction (a j x) (b l x)
          (fun k => u k x) (fun m => v m x) (fun k m => G k m x))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * X)
  refine ⟨C, hC, ?_⟩
  intro σ J K L M _ _ _ _ s p a u b v G hp E F hG j l
  classical
  let t := p + (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
  have hAt : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hterm (km : K × M) : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
      ((t + A) ^ A) (fun x =>
        (a j x * star (u km.1 x)) * star (b l x * star (v km.2 x)) * G km.1 km.2 x)) := by
    obtain ⟨H⟩ := hmul hp (Classical.choice (E.expansion j km.1))
      (Classical.choice (F.expansion l km.2)).conjugate
    exact hmul ht (H.mono hAt) ((Classical.choice (hG km.1 km.2)).mono hpt)
  have hcard : (Fintype.card (K × M) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul E.right_dimension F.right_dimension (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, two_mul]
  have hc : (∑ _ : K × M, ‖(1 : ℂ)‖) ≤ Real.exp (2 * p) := by simpa using hcard
  have H := NativeIntegerExpansion.weightedSum (fun km => Classical.choice (hterm km))
    (fun _ => 1) (by positivity : 0 ≤ 2 * p) hcard hc
  have hcost : (t + A) ^ A + 2 * p ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by simpa only [one_mul, complexCrossContraction] using H.mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem division_dilation_integer_representative (d : ℕ) [NeZero d]
    {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter bound p) (x : σ → ℤ) (j : Fin W.outputDim) :
    (W.rationalDilation ((d : ℚ)⁻¹)).eval j (fun i => x i - ((x i : ZMod d).val : ℤ)) =
      W.eval j (fun i => x i / (d : ℤ)) := by
  have hx : (fun i => x i - ((x i : ZMod d).val : ℤ)) =
      (fun i => (d : ℤ) * (x i / (d : ℤ))) := by
    funext i
    rw [ZMod.val_intCast, sub_eq_iff_eq_add]
    simpa only [add_comm] using (Int.emod_add_mul_ediv (x i) (d : ℤ)).symm
  rw [hx]
  apply W.rationalDilation_eval_rescaled
  rw [Int.cast_natCast]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ}

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped BigOperators

theorem exists_sampled_rational_division_equivalence (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] (bound : σ → ℕ),
      (∑ k, bound k) = s + 1 → ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter bound p) (ρ : σ → Fin 2),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) => (W.rationalDilation ((d : ℚ)⁻¹)).eval j (fun k => x (ρ k)))
        (fun j x => W.eval j (fun k => x (ρ k) / (d : ℤ))) := by
  obtain ⟨A, _, hshift⟩ := exists_multidegree_integer_translation s
  obtain ⟨B, _, hresidue⟩ := exists_pairResidueIndicator_expansion d s hs
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + Polynomial.C B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C D) ^ D + T + Polynomial.C (d ^ 2))
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hdegree p W ρ
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let V := W.rationalDilation ((d : ℚ)⁻¹)
  let t : ℝ := (p + A) ^ A + B + p + 2
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hat : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hbt : (B : ℝ) ≤ t := by dsimp [t]; linarith
  have hbound : (t + D) ^ D + t + (d : ℝ) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (t + D) ^ D := by positivity
  have hpc : p ≤ (p + C) ^ C := by
    have hpt : p ≤ t := by dsimp [t]; linarith
    linarith [sq_nonneg (d : ℝ)]
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpc)
  refine ⟨hdim, hdim, ?_⟩
  intro i j
  let inp (x : Fin 2 → ℤ) : σ → ℤ := fun k => x (ρ k)
  have hinput (x : Fin 2 → ℤ) : (fun k => x (ρ k)) = inp x := rfl
  let F (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) :=
    V.eval i (inp x) * star (V.eval j (inp (fun k => x k - ((r k).val : ℤ))))
  have hF (r : Fin 2 → ZMod d) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s t (F r)) := by
    obtain ⟨E⟩ := ((hshift bound hdegree V 0 (fun k => -((r (ρ k)).val : ℤ))).coordinatePullback ρ).expansion i j
    have hr (x : Fin 2 → ℤ) :
        (fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ)) =
          inp (fun k => x k - ((r k).val : ℤ)) := by
      calc
        _ = (fun k => x (ρ k) - ((r (ρ k)).val : ℤ)) := by
          funext k
          simp only [Pi.add_apply, sub_eq_add_neg]
        _ = _ := hinput (fun k => x k - ((r k).val : ℤ))
    have heq : (fun x : Fin 2 → ℤ => V.eval i ((fun k => x (ρ k)) + 0) *
        star (V.eval j ((fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ))))) = F r := by
      funext x
      rw [add_zero, hr, hinput]
    exact ⟨heq ▸ E.mono hat⟩
  have hterm (r : Fin 2 → ZMod d) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s
      ((t + D) ^ D) (fun x => pairResidueIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hbt) (Classical.choice (hF r))
  have hcoeff : (∑ _ : Fin 2 → ZMod d, ‖(1 : ℂ)‖) ≤ Real.exp ((d : ℝ) ^ 2) := by
    simpa using card_pairResidue_le_exp d
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hterm r)) (fun _ => 1)
    (sq_nonneg (d : ℝ)) (card_pairResidue_le_exp d) hcoeff
  have hrep (x : Fin 2 → ℤ) :
      V.eval j (inp (fun k => x k - ((x k : ZMod d).val : ℤ))) =
        W.eval j (inp (fun k => x k / (d : ℤ))) := by
    exact division_dilation_integer_representative d W (inp x) j
  have heq : (fun x => ∑ r : Fin 2 → ZMod d, (1 : ℂ) * (pairResidueIndicator r x * F r x)) =
      (fun x => V.eval i (inp x) * star (W.eval j (inp (fun k => x k / (d : ℤ))))) := by
    funext x
    let r : Fin 2 → ZMod d := fun k => (x k : ZMod d)
    rw [Finset.sum_eq_single r]
    · simp only [pairResidueIndicator, r, ite_true, one_mul, F, hrep]
    · intro z _ hz
      have hne : (fun k => (x k : ZMod d)) ≠ z := fun h => hz h.symm
      simp only [pairResidueIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  rw [heq] at S
  exact ⟨S.mono (by linarith)⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ}

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedAntisymmetricBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_mixed_tuple {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin (n + 2) → X) → ℂ) :
    (𝔼 x, F x) = 𝔼 u : Fin n → X, 𝔼 h, 𝔼 m, F (Fin.cons h (Fin.cons m u)) := by
  simp_rw [expect_dependent_fin_cons]
  calc
    _ = 𝔼 h, 𝔼 u : Fin n → X, 𝔼 m, F (Fin.cons h (Fin.cons m u)) :=
      Finset.expect_congr rfl (fun _ _ => Finset.expect_comm _ _ _)
    _ = _ := Finset.expect_comm _ _ _

namespace NativeMultidegreeNilcharacter

theorem exists_mixed_sum_antisymmetric_box (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ j k : Fin W.outputDim, Real.exp (-((p + C) ^ C)) ≤
        (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
          W.mixedAntisymmetric j k (fun l => (x l).val))).re := by
  obtain ⟨a, _, hcorr⟩ := exists_mixed_sum_antisymmetric_correlation n
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Polynomial.C (2 ^ (n + 2)) * Q)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hinput
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨j, k, B, hB, hBind, hpositive⟩ := hcorr W f hf i A hA hmiss hinput
  let F (x : Fin (n + 2) → ZMod N) := W.mixedAntisymmetric j k (fun l => (x l).val)
  let U (l : Fin (n + 2)) (x : Fin (n + 2) → ZMod N) := B l (fun l => (x l).val)
  have hvals (h m : ZMod N) (u : Fin n → ZMod N) :
      (fun l => (((Fin.cons h (Fin.cons m u) : Fin (n + 2) → ZMod N) l).val : ℤ)) =
        Fin.cons (h.val : ℤ) (Fin.cons (m.val : ℤ) (fun l => (u l).val)) := by
    funext l
    refine Fin.cases ?_ (fun l => ?_) l
    · rfl
    · refine Fin.cases ?_ (fun l => ?_) l <;> rfl
  have hmean : boxTestCorrelation F U =
      𝔼 u : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        W.mixedAntisymmetric j k (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun l => (u l).val))) *
          ∏ l, B l (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun j => (u j).val))) := by
    rw [boxTestCorrelation, expect_mixed_tuple]
    simp only [F, U, hvals]
  have hU : ∀ l, MissesBoxCoordinate (U l) l := by
    intro l x v
    apply hBind l
    intro m hml
    change (((Function.update x l v) m).val : ℤ) = ((x m).val : ℤ)
    rw [Function.update_of_ne hml]
  have hbox := boxTest_cauchySchwarz (n + 1) F U (fun l x => hB l _) hU
  have hscore : Real.exp (-((2 ^ (n + 2) : ℕ) : ℝ) * ((p + a) ^ a)) ≤
      (boxPhaseMoment (n + 2) F).re := by
    have hpower : Real.exp (-((2 ^ (n + 2) : ℕ) : ℝ) * ((p + a) ^ a)) =
        Real.exp (-((p + a) ^ a)) ^ (2 ^ (n + 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpower]
    apply (pow_le_pow_left₀ (Real.exp_nonneg _) ?_ _).trans hbox
    rwa [hmean]
  have hcost : ((2 ^ (n + 2) : ℕ) : ℝ) * ((p + a) ^ a) ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨j, k, ?_⟩
  exact (Real.exp_le_exp.mpr (by linarith)).trans hscore

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MixedSumKernelCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_mixed_kernel_correlation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp (-p) ≤ (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
        W.mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))).re →
      Nonempty (NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        Finset.univ (fun x : Fin (n + 2) → ZMod N => fun k => ((x k).val : ℤ))
        (fun x => W.mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))) := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_mixed_anchor_expansion n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hbias
  let K := W.mixedAntisymmetric i j
  let Kc := fun x : Fin (n + 2) → ZMod N => K (fun k => ((x k).val : ℤ))
  obtain ⟨a, ha⟩ := exists_box_corner_anchor_correlation Kc
  obtain ⟨E⟩ := hanchor W i j (fun k => ((a k).val : ℤ))
  have hmap (x : Fin (n + 2) → ZMod N) : boxCornerAnchor Kc a x =
      boxCornerAnchor K (fun k => ((a k).val : ℤ)) (fun k => ((x k).val : ℤ)) :=
    boxCornerAnchor_map (fun z : ZMod N => (z.val : ℤ)) K a x
  have hcorr : Real.exp (-p) ≤ ‖𝔼 x : Fin (n + 2) → ZMod N,
      K (fun k => ((x k).val : ℤ)) *
        star (star (boxCornerAnchor K (fun k => ((a k).val : ℤ))
          (fun k => ((x k).val : ℤ))))‖ := by
    have h := hbias.trans ha
    simp_rw [hmap] at h
    simpa only [Kc, star_star] using h
  obtain ⟨S⟩ := NativeSampleCorrelation.exists_of_expansion E.conjugate hp hcorr
  have hcost : p + (p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨S.mono hcost⟩

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_sum_kernel_correlation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ j k : Fin W.outputDim,
        Nonempty (NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
          Finset.univ (fun x : Fin (n + 2) → ZMod N => fun l => ((x l).val : ℤ))
          (fun x => W.mixedAntisymmetric j k (fun l => ((x l).val : ℤ)))) := by
  obtain ⟨a, _, hbox⟩ := exists_mixed_sum_antisymmetric_box n
  obtain ⟨b, _, hkernel⟩ := exists_mixed_kernel_correlation n
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let R := X + Q + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  obtain ⟨j, k, hmoment⟩ := hbox W f hf i A hA hmiss hcorr
  have hmono (x : Fin (n + 2) → ℤ) :
      (W.mono hpr).mixedAntisymmetric j k x = W.mixedAntisymmetric j k x := rfl
  have hinput : Real.exp (-r) ≤
      (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
        (W.mono hpr).mixedAntisymmetric j k (fun l => (x l).val))).re := by
    simpa only [hmono] using (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans hmoment
  obtain ⟨S⟩ := hkernel hr (W.mono hpr) j k hinput
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨j, k, ⟨S.mono hcost⟩⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

def mixedSampledInput {d : ℕ} (π : Fin (d + 3) → Fin 2) (x : Fin 2 → ℤ) :
    MixedReplicatedIndex (d + 2) → ℤ :=
  mixedReplicatedInput (x (π 0)) (fun j => x (π j.succ))

theorem mixedSampledInput_slots {d : ℕ} (π : Fin (d + 3) → Fin 2) (x : Fin 2 → ℤ) :
    mixedSampledInput π x =
      mixedSlotInput (x (π 0)) (x (π 1)) (fun j => x (π j.succ.succ)) := by
  unfold mixedSampledInput mixedSlotInput
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem mixedSampledInput_coordinates {d : ℕ} (π : Fin (d + 3) → Fin 2) (x : Fin 2 → ℤ) :
    (fun j => x (π (mixedInputCoordinate (d + 1) j))) = mixedSampledInput π x := by
  exact (mixedInputCoordinate_eval (d + 1) (fun k => x (π k))).trans
    (mixedSampledInput_slots π x).symm

def mixedPermuteSample {d : ℕ} (e : Equiv.Perm (Fin (d + 2)))
    (π : Fin (d + 3) → Fin 2) : Fin (d + 3) → Fin 2 :=
  Fin.cases (π 0) (fun j => π (e j).succ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedCoordinateIndex_coordinate (n : ℕ) (j : MixedReplicatedIndex (n + 1)) :
    mixedCoordinateIndex n (mixedInputCoordinate n j) = j := by
  rcases mixedReplicated_cases j with rfl | ⟨k, rfl⟩
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

def mixedAllCoordinates (s : ℕ) : List (MixedReplicatedIndex (s + 2)) :=
  List.ofFn (mixedCoordinateIndex (s + 1))

theorem mixedAllCoordinates_length (s : ℕ) : (mixedAllCoordinates s).length = s + 3 := by
  simp only [mixedAllCoordinates, List.length_ofFn]

theorem mixedAllCoordinates_nodup (s : ℕ) : (mixedAllCoordinates s).Nodup := by
  apply List.nodup_ofFn.mpr
  exact Function.LeftInverse.injective (mixedInputCoordinate_index (s + 1))

theorem mixedAllCoordinates_get (s : ℕ) (j : Fin (mixedAllCoordinates s).length) :
    (mixedAllCoordinates s).get j =
      mixedCoordinateIndex (s + 1) (Fin.cast (mixedAllCoordinates_length s) j) := by
  exact List.get_ofFn (mixedCoordinateIndex (s + 1)) j

theorem mem_mixedAllCoordinates (s : ℕ) (j : MixedReplicatedIndex (s + 2)) :
    j ∈ mixedAllCoordinates s := by
  apply List.mem_ofFn.mpr
  exact ⟨mixedInputCoordinate (s + 1) j, mixedCoordinateIndex_coordinate (s + 1) j⟩

def mixedCornerAssignmentEquiv (s : ℕ) :
    (Fin (mixedAllCoordinates s).length → Fin 2) ≃ (Fin (s + 3) → Fin 2) where
  toFun v j := v (Fin.cast (mixedAllCoordinates_length s).symm j)
  invFun v j := v (Fin.cast (mixedAllCoordinates_length s) j)
  left_inv v := by funext j; rfl
  right_inv v := by funext j; rfl

def mixedDiagonalCorner {s : ℕ} (v : Fin (s + 3) → Fin 2) (x : Fin 2 → ℤ) :
    MixedReplicatedIndex (s + 2) → ℤ := mixedSampledInput (fun k => (v k).rev) x

theorem mixedDiagonalCorner_zero {s : ℕ} (x : Fin 2 → ℤ) :
    mixedDiagonalCorner (fun _ : Fin (s + 3) => 0) x = fun _ => x 1 := by
  rw [mixedDiagonalCorner, ← mixedSampledInput_coordinates]
  rfl

def mixedDiagonalChoiceInput {s : ℕ} (x : Fin 2 → ℤ)
    (j : Fin 2 × MixedReplicatedIndex (s + 2)) : ℤ := x j.1.rev

theorem mixedDiagonalChoice_sum (s : ℕ) (x : Fin 2 → ℤ) :
    finiteChoiceCoordinateInput (mixedAllCoordinates s) (mixedDiagonalChoiceInput x) =
      fun _ => x 1 + x 0 := by
  funext j
  simp only [finiteChoiceCoordinateInput, mem_mixedAllCoordinates, ite_true,
    mixedDiagonalChoiceInput]
  change (∑ a : Fin 2, x a.rev) = x 1 + x 0
  exact Fin.sum_univ_two (fun a : Fin 2 => x a.rev)

theorem mixedDiagonalChoice_leaf (s : ℕ) (x : Fin 2 → ℤ)
    (v : Fin (mixedAllCoordinates s).length → Fin 2) :
    finiteChoiceLeafInput (mixedAllCoordinates s) v (mixedDiagonalChoiceInput x) =
      mixedDiagonalCorner (mixedCornerAssignmentEquiv s v) x := by
  rw [mixedDiagonalCorner, ← mixedSampledInput_coordinates]
  funext j
  let k : Fin (mixedAllCoordinates s).length :=
    Fin.cast (mixedAllCoordinates_length s).symm (mixedInputCoordinate (s + 1) j)
  have H := finiteChoiceLeafInput_get (mixedAllCoordinates s)
    (mixedAllCoordinates_nodup s) v (mixedDiagonalChoiceInput x) k
  rw [mixedAllCoordinates_get] at H
  have hk : mixedCoordinateIndex (s + 1) (Fin.cast (mixedAllCoordinates_length s) k) = j :=
    mixedCoordinateIndex_coordinate (s + 1) j
  rw [hk] at H
  exact H

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedDiagonalTensor
    (a : (Fin (s + 3) → Fin 2) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∏ v, W.eval (a v) (mixedDiagonalCorner v x)

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_diagonal_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p),
      NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
        W.mixedDiagonalTensor := by
  let : Nonempty (MixedReplicatedIndex (s + 2)) := replicatedMixed_nonempty (s + 2)
  obtain ⟨C, hC, hexpand⟩ := exists_finite_assignment_equivalence 1 (mixedAllCoordinates s)
  refine ⟨C, hC, ?_⟩
  intro p W
  let a : Fin 2 × MixedReplicatedIndex (s + 2) → Fin 2 := fun j => j.1.rev
  have hA (x : Fin 2 → ℤ) : (fun j => x (a j)) = mixedDiagonalChoiceInput x := rfl
  have E := (hexpand W (mixedAllCoordinates_nodup s)).coordinatePullback a
  have H : NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C)
      (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
      (fun b : (Fin (mixedAllCoordinates s).length → Fin 2) → Fin W.outputDim =>
        fun x => ∏ v, W.eval (b v) (mixedDiagonalCorner (mixedCornerAssignmentEquiv s v) x)) := by
    simpa only [hA, finiteChoiceExpansion, mixedDiagonalChoice_sum, mixedDiagonalChoice_leaf,
      replicatedMixed_card, Nat.add_sub_cancel] using E
  have hdim : (Fintype.card ((Fin (s + 3) → Fin 2) → Fin W.outputDim) : ℝ) ≤
      Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fun, Fintype.card_fin, mixedAllCoordinates_length]
      using H.right_dimension
  apply H.of_coordinate_maps _ W.mixedDiagonalTensor id
    (fun b v => b (mixedCornerAssignmentEquiv s v)) (fun _ _ => rfl) _
    H.left_dimension hdim le_rfl
  intro b x
  exact ((mixedCornerAssignmentEquiv s).prod_comp
    (fun v => W.eval (b v) (mixedDiagonalCorner v x))).symm

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

abbrev MixedNonconstantCorner (s : ℕ) := {v : Fin (s + 3) → Fin 2 // v ≠ fun _ => 0}

theorem mixedNonconstantCorner_card (s : ℕ) :
    Fintype.card (MixedNonconstantCorner s) = 2 ^ (s + 3) - 1 := by
  simp [MixedNonconstantCorner, Fintype.card_subtype_compl]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedDiagonalDerivative (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0))

noncomputable def mixedNonconstantTensor (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.eval (a v) (mixedDiagonalCorner v.val x))

theorem mixedDiagonalDerivative_norm (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedDiagonalDerivative a x‖ ≤ 1 := by
  rw [mixedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedNonconstantTensor_norm (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedNonconstantTensor a x‖ ≤ 1 := by
  rw [mixedNonconstantTensor, norm_star, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedNonconstantTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : MixedNonconstantCorner s → Fin W.outputDim, ‖W.mixedNonconstantTensor a x‖ ^ 2 = 1 := by
  simp only [mixedNonconstantTensor, norm_star, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ v : MixedNonconstantCorner s, ∑ a : Fin W.outputDim,
        ‖W.eval a (mixedDiagonalCorner v.val x)‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem exists_mixed_diagonal_derivative_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p),
      NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C)
        W.mixedDiagonalDerivative W.mixedNonconstantTensor := by
  obtain ⟨A, _, hdiag⟩ := exists_mixed_diagonal_expansion s
  let m : ℕ := 2 ^ (s + 3) - 1
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C m * X + 2 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hsum : (p + A) ^ A + (m : ℝ) * p + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hm : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have htwo : 2 * p ≤ (p + C) ^ C := by linarith
  have hnonconstant : (m : ℝ) * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hdimNonconstant : (Fintype.card (MixedNonconstantCorner s → Fin W.outputDim) : ℝ) ≤
      Real.exp ((m : ℝ) * p) := by
    simp only [Fintype.card_fun, mixedNonconstantCorner_card, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound m
      _ = _ := (Real.exp_nat_mul p m).symm
  refine ⟨(card_product_le_exp_two hdim hdim).trans (Real.exp_le_exp.mpr htwo),
    hdimNonconstant.trans (Real.exp_le_exp.mpr hnonconstant), ?_⟩
  intro a b
  let full : (Fin (s + 3) → Fin 2) → Fin W.outputDim := fun v =>
    if h : v = fun _ => 0 then a.1 else b ⟨v, h⟩
  obtain ⟨F⟩ := (hdiag W).expansion a.2 full
  have htensor (x : Fin 2 → ℤ) : W.mixedDiagonalTensor full x =
      W.eval a.1 (fun _ => x 1) *
        ∏ v : MixedNonconstantCorner s, W.eval (b v) (mixedDiagonalCorner v.val x) := by
    rw [mixedDiagonalTensor, Fintype.prod_eq_mul_prod_subtype_ne _ (fun _ => 0)]
    have hzero : full (fun _ => 0) = a.1 := by simp only [full, dif_pos rfl]
    have hfull (v : MixedNonconstantCorner s) : full v.val = b v := by
      simp only [full, dif_neg v.property]
    simp only [hzero, mixedDiagonalCorner_zero, hfull]
  have heq : (fun x : Fin 2 → ℤ => star (W.eval a.2 (fun _ => x 1 + x 0) *
      star (W.mixedDiagonalTensor full x))) =
      (fun x => W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor b x)) := by
    funext x
    rw [htensor]
    simp only [mixedDiagonalDerivative, mixedNonconstantTensor, star_mul, star_star]
    ring
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedReplicated_totalDegree (n : ℕ) :
    (∑ _ : MixedReplicatedIndex (n + 1), (1 : ℕ)) = n + 2 := by
  have hc : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 := replicatedMixed_card (n + 1)
  rw [Finset.sum_const, Finset.card_univ, hc]
  simp

namespace NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {n : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)

noncomputable def mixedPairComponent (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2)) :
    W.model.Niltest (fun _ : Fin (n + 2) => 1) :=
  (W.component out).linearPullbackHom (fun j =>
    { toFun := fun x => x (v (mixedInputCoordinate n j))
      map_zero' := rfl
      map_add' := fun _ _ => rfl })

theorem mixedPairComponent_eval (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2))
    (x : Fin (n + 2) → ℤ) :
    (W.mixedPairComponent out v).eval x =
      W.eval out (mixedSlotInput (x (v 0)) (x (v 1)) (fun j => x (v j.succ.succ))) := by
  rw [mixedPairComponent, Niltest.eval_linearPullbackHom, component_eval]
  exact congrArg (W.eval out) (mixedInputCoordinate_eval n (fun j => x (v j)))

theorem mixedPairComponent_complexity (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2)) :
    (W.mixedPairComponent out v).ComplexityLE (p + 4) := W.component_complexity out

theorem mixedPairComponent_vertical (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2))
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : W.model.Space) :
    (W.mixedPairComponent out v).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.mixedPairComponent out v).observable x := by
  exact W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def mixedIntegrationRoot {d : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p) :
    NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1)
      (tensorPowerBudget ((d + 3) ^ (d + 2)) p) :=
  (W.rationalDilation (((d + 3 : ℕ) : ℚ)⁻¹)).tensorPower ((d + 3) ^ (d + 2))

theorem exists_mixed_integration_root_equivalence (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        W.eval (tensorVector W.mixedIntegrationRoot.eval (d + 3)) := by
  obtain ⟨a, _, hdilation⟩ := exists_uniform_dilation_degree_equivalence (d + 2) ((d + 3 : ℕ) : ℤ)
  let n := (d + 3) ^ (d + 2)
  let X : Polynomial ℕ := Polynomial.X
  let B := Polynomial.C (n + 1) * (X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (d + 4) * B + X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + a) ^ a := by positivity
  have hB : 0 ≤ tensorPowerBudget n p := by unfold tensorPowerBudget; positivity
  have hqB : 0 ≤ (d + 3 : ℝ) * tensorPowerBudget n p := by positivity
  have hb : (p + a) ^ a + (d + 4 : ℝ) * tensorPowerBudget n p + p + 2 ≤ (p + C) ^ C := by
    simpa [X, B, tensorPowerBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith
  have hAr : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith
  have hdimBound : (d + 3 : ℝ) * tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  let V := W.rationalDilation (((d + 3 : ℕ) : ℚ)⁻¹)
  let R := V.tensorPower n
  have hscale : (((d + 3 : ℕ) : ℚ)⁻¹) * (((d + 3 : ℕ) : ℤ) : ℚ) = 1 := by
    rw [Int.cast_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  have hleft (i : Fin W.outputDim) (x : MixedReplicatedIndex (d + 2) → ℤ) :
      W.eval i x = integerDilationVector V.eval ((d + 3 : ℕ) : ℤ) i x :=
    (W.rationalDilation_eval_rescaled _ _ hscale i x).symm
  have hpos : 1 ≤ d + 3 := by omega
  have hright (b : Fin (d + 3) → Fin R.outputDim) (x : MixedReplicatedIndex (d + 2) → ℤ) :
      tensorVector R.eval (d + 3) b x = signedTensorVector V.eval (((d + 3 : ℕ) : ℤ) ^ (d + 3))
        (rootTensorIndex W.outputDim (d + 3) (d + 3) hpos b) x := by
    exact V.tensorPower_tensor_eval (d + 3) (d + 3) hpos b x
  have hdim : (Fintype.card (Fin (d + 3) → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ (d + 3) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) R.output_bound _
      _ = Real.exp ((d + 3 : ℝ) * tensorPowerBudget n p) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget n p) (d + 3)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimBound
  have hs : (∑ _ : MixedReplicatedIndex (d + 2), (1 : ℕ)) = d + 3 :=
    mixedReplicated_totalDegree (d + 1)
  exact (hdilation _ hs V).of_coordinate_maps W.eval (tensorVector R.eval (d + 3)) id
    (rootTensorIndex W.outputDim (d + 3) (d + 3) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedCyclicDiagonalDerivative {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) : ℂ :=
  W.eval a.1 (fun _ => ((x 1).val : ℤ)) *
    star (W.eval a.2 (fun _ => ((x 0 + x 1).val : ℤ)))

theorem mixedCyclicDiagonalDerivative_norm {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.mixedCyclicDiagonalDerivative a x‖ ≤ 1 := by
  rw [mixedCyclicDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedCyclicDiagonalDerivative_unit {N : ℕ} [NeZero N]
    (x : Fin 2 → ZMod N) :
    ∑ a : Fin W.outputDim × Fin W.outputDim, ‖W.mixedCyclicDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [mixedCyclicDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

noncomputable def mixedWrappedDiagonalDerivative (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0 - N))

noncomputable def mixedDiagonalWrapCoefficient (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval k (fun _ => x 1 + x 0) * star (W.eval j (fun _ => x 1 + x 0 - N))

theorem mixedWrappedDiagonalDerivative_norm (N : ℕ) (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedWrappedDiagonalDerivative N a x‖ ≤ 1 := by
  simp only [mixedWrappedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedDiagonalWrapCoefficient_norm (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedDiagonalWrapCoefficient N j k x‖ ≤ 1 := by
  simp only [mixedDiagonalWrapCoefficient, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedWrappedDiagonalDerivative_resolution (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedWrappedDiagonalDerivative N a x =
      ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x * W.mixedDiagonalDerivative (a.1, k) x := by
  have h := complex_unit_vector_resolution
    (fun k => W.eval k (fun _ => x 1 + x 0)) (W.unit_eval _)
    (star (W.eval a.2 (fun _ => x 1 + x 0 - N)))
  calc
    _ = W.eval a.1 (fun _ => x 1) *
        ∑ k, (star (W.eval a.2 (fun _ => x 1 + x 0 - N)) *
          star (W.eval k (fun _ => x 1 + x 0))) * W.eval k (fun _ => x 1 + x 0) := by
      rw [← h]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [mixedDiagonalWrapCoefficient, mixedDiagonalDerivative]
      ring

theorem mixedCyclicDiagonalDerivative_branches {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    W.mixedCyclicDiagonalDerivative a x =
      (1 - (cyclicCarry (x 0) (x 1) : ℂ)) *
          W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) +
        (cyclicCarry (x 0) (x 1) : ℂ) *
          W.mixedWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) := by
  have hval := cyclic_representative_add (x 0) (x 1)
  have hlt := (x 0).val_lt
  by_cases hw : N ≤ (x 0).val + (x 1).val
  · have hcut : N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      mixedCyclicDiagonalDerivative, mixedWrappedDiagonalDerivative]
    rw [hval, if_pos hcut]
  · have hcut : ¬N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      mixedCyclicDiagonalDerivative, mixedDiagonalDerivative]
    rw [hval, if_neg hcut, sub_zero]

theorem exists_mixedDiagonalWrapCoefficient_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p) (N : ℕ)
      (j k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + C) ^ C)
        (W.mixedDiagonalWrapCoefficient N j k)) := by
  obtain ⟨C, hC, htranslate⟩ := exists_multidegree_integer_translation (s + 2)
  refine ⟨C, hC, ?_⟩
  intro p W N j k
  let A : MixedReplicatedIndex (s + 2) → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1 + x 0, map_zero' := by simp,
      map_add' := fun x y => by simp only [Pi.add_apply]; ring }
  obtain ⟨F⟩ := (htranslate (fun _ : MixedReplicatedIndex (s + 2) => 1) (mixedReplicated_totalDegree (s + 1)) W 0 (fun _ => -(N : ℤ))).expansion k j
  have H := F.linearPullbackHom A
  have heq : (fun x : Fin 2 → ℤ => W.eval k ((fun l => A l x) + 0) *
      star (W.eval j ((fun l => A l x) + fun _ => -(N : ℤ)))) =
      W.mixedDiagonalWrapCoefficient N j k := by
    funext x
    simp only [add_zero, mixedDiagonalWrapCoefficient, sub_eq_add_neg]
    rfl
  exact ⟨heq ▸ H⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_rational_division_equivalence (d D : ℕ) [NeZero D] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)
      (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) =>
          (W.rationalDilation ((D : ℚ)⁻¹)).eval j (mixedSampledInput π x))
        (fun j x => W.eval j (mixedSampledInput π (fun k => x k / (D : ℤ)))) := by
  obtain ⟨C, hC, h⟩ := exists_sampled_rational_division_equivalence D (d + 2) (by omega)
  refine ⟨C, hC, ?_⟩
  intro p W π
  simpa only [← mixedSampledInput_coordinates] using
    h (fun _ : MixedReplicatedIndex (d + 2) => 1) (mixedReplicated_totalDegree (d + 1)) W
      (fun j => π (mixedInputCoordinate (d + 1) j))

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

def mixedPairBudget (p q : ℝ) : ℝ := 4 * (p + q + 1) + raisedNiltestBudget (p + q) + 6

namespace NativeSampleCorrelation

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

abbrev MixedPairAlgebra := ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

noncomputable def mixedPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ _ : MixedReplicatedIndex (n + 1), 1) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)) (fun _ : Fin 2 => W.model)

noncomputable def mixedPairTests :
    ∀ k, (V.mixedPairModels k).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).conjugate
  | some k => ![W.mixedPairComponent i id,
      (W.mixedPairComponent j (mixedExchangeCoordinate n)).conjugate] k

noncomputable def mixedPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![W.vertical.frequency, -W.vertical.frequency] k

theorem mixedPairTests_eval (x : Fin (n + 2) → ℤ) :
    (∏ k, (V.mixedPairTests k).eval x) =
      W.mixedAntisymmetric i j x * star (V.test.eval x) := by
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).conjugate.eval x *
    ((W.mixedPairComponent i id).eval x *
      (W.mixedPairComponent j (mixedExchangeCoordinate n)).conjugate.eval x) = _
  rw [Niltest.eval_conjugate, Niltest.raiseStep_eval, Niltest.eval_conjugate,
    W.mixedPairComponent_eval, W.mixedPairComponent_eval]
  have h0 : mixedExchangeCoordinate n 0 = 1 := rfl
  have h1 : mixedExchangeCoordinate n 1 = 0 := rfl
  have ht (k : Fin n) : mixedExchangeCoordinate n k.succ.succ = k.succ.succ := rfl
  simp only [id_eq, h0, h1, ht, NativeMultidegreeNilcharacter.mixedAntisymmetric]
  ring

theorem mixedPairTests_vertical (k : Option (Fin 2))
    (z : (V.mixedPairModels k).RealGroup)
    (hz : z ∈ (V.mixedPairModels k).filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : (V.mixedPairModels k).Space) :
    (V.mixedPairTests k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.mixedPairFrequencies k) z.coord : ℝ) : CircleFourier.Circle) *
          (V.mixedPairTests k).observable x := by
  cases k with
  | none =>
    exact V.test.conjugate.raiseStep_top_vertical
      (by rw [mixedReplicated_totalDegree]; omega : n + 1 < ∑ _ : MixedReplicatedIndex (n + 1), 1) z hz x
  | some k =>
    fin_cases k
    · exact W.mixedPairComponent_vertical i id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.mixedPairComponent_vertical j (mixedExchangeCoordinate n)) z hz x

include V in
theorem mixedPairBudget_six_le : 6 ≤ mixedPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  unfold mixedPairBudget raisedNiltestBudget
  nlinarith [sq_nonneg (p + q + 2)]

theorem mixedPairTests_complexity (k : Option (Fin 2)) :
    (V.mixedPairTests k).ComplexityLE (mixedPairBudget p q) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have hr : 0 ≤ raisedNiltestBudget (p + q) := hpq.trans (le_raisedNiltestBudget _)
  cases k with
  | none =>
    exact (V.test.raiseStep_complexity (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1) hpq
      (V.complexity.mono (le_add_of_nonneg_left hp))).mono
        (by unfold mixedPairBudget; linarith)
  | some k =>
    have hcost : p + 4 ≤ mixedPairBudget p q := by
      unfold mixedPairBudget
      linarith
    fin_cases k
    · exact (W.mixedPairComponent_complexity i id).mono hcost
    · exact (W.mixedPairComponent_complexity j (mixedExchangeCoordinate n)).mono hcost

end NativeSampleCorrelation
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_original_mixed_root_equivalence (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      NativeIntegerVectorEquivalence (d + 2) p M.eval
        (fun k x => W.eval k (fun j => x j.1)) →
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C) M.eval
        (fun a (x : Fin 2 → ℤ) => tensorVector W.mixedIntegrationRoot.eval (d + 3) a (fun j => x j.1)) := by
  obtain ⟨a, _, hroot⟩ := exists_mixed_integration_root_equivalence d
  obtain ⟨b, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p M W E
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + a) ^ a + p
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_left (by positivity)
  have hAt : (p + a) ^ a ≤ t := le_add_of_nonneg_right hp
  have F := (hroot W).coordinatePullback (fun j : MixedReplicatedIndex (d + 2) => j.1)
  have H := htrans ht (E.mono hpt) (F.mono hAt) (fun x => W.unit_eval _)
  have hcost : (t + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedSwapSample {s : ℕ} (π : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  fun k => π (mixedExchangeCoordinate (s + 1) k)

theorem mixedSwapSample_input {s : ℕ} (π : Fin (s + 3) → Fin 2) (x : Fin 2 → ℤ) :
    mixedSampledInput (mixedSwapSample π) x =
      mixedSlotInput (x (π 1)) (x (π 0)) (fun j => x (π j.succ.succ)) := by
  rw [mixedSampledInput_slots]
  rfl

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def divisionMixedExchangeCorrection (d : ℕ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  complexCrossContraction
    ((W.rationalDilation ((d : ℚ)⁻¹)).eval a (mixedSampledInput π x))
    ((W.rationalDilation ((d : ℚ)⁻¹)).eval b (mixedSampledInput (mixedSwapSample π) x))
    (fun i => W.eval i (mixedSampledInput π (fun k => x k / (d : ℤ))))
    (fun j => W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => x k / (d : ℤ))))
    (fun i j => G π i j (fun k => x k / (d : ℤ)))

theorem divisionMixedExchangeCorrection_pointwise_error (d : ℕ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖(W.rationalDilation ((d : ℚ)⁻¹)).eval a (mixedSampledInput π x) *
        star ((W.rationalDilation ((d : ℚ)⁻¹)).eval b (mixedSampledInput (mixedSwapSample π) x)) -
      W.divisionMixedExchangeCorrection d G π a b x‖ ≤
      ∑ ij : Fin W.outputDim × Fin W.outputDim,
        ‖W.eval ij.1 (mixedSampledInput π (fun k => x k / (d : ℤ))) *
            star (W.eval ij.2 (mixedSampledInput (mixedSwapSample π) (fun k => x k / (d : ℤ)))) -
          G π ij.1 ij.2 (fun k => x k / (d : ℤ))‖ := by
  exact norm_sub_complexCrossContraction_le_sum _ _ _ _ _
    ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _) ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)
    (W.unit_eval _) (W.unit_eval _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)

theorem divisionMixedExchangeCorrection_mean_error (d : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.rationalDilation ((d : ℚ)⁻¹)).eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star ((W.rationalDilation ((d : ℚ)⁻¹)).eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.divisionMixedExchangeCorrection d G π a b (fun k => ((x k).val : ℤ))‖) ≤
      (d : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε := by
  have hmean := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.divisionMixedExchangeCorrection_pointwise_error d G π a b
      (fun k => ((x k).val : ℤ)))
  rw [Finset.expect_sum_comm] at hmean
  have he (ij : Fin W.outputDim × Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N,
        ‖W.eval ij.1 (mixedSampledInput π (fun k => ((x k).val : ℤ) / (d : ℤ))) *
            star (W.eval ij.2 (mixedSampledInput (mixedSwapSample π)
              (fun k => ((x k).val : ℤ) / (d : ℤ)))) -
          G π ij.1 ij.2 (fun k => ((x k).val : ℤ) / (d : ℤ))‖) ≤ (d : ℝ) ^ 2 * ε := by
    have h := expect_pair_cyclicDivision_le d (fun x : Fin 2 → ZMod N =>
      ‖W.eval ij.1 (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval ij.2 (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π ij.1 ij.2 (fun k => ((x k).val : ℤ))‖) (fun _ => norm_nonneg _)
    simp only [cyclicDivision_val, Int.natCast_ediv] at h
    exact h.trans (mul_le_mul_of_nonneg_left (herr π ij.1 ij.2) (sq_nonneg _))
  apply hmean.trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, (d : ℝ) ^ 2 * ε :=
      Finset.sum_le_sum (fun ij _ => he ij)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

theorem divisionMixedExchangeCorrection_norm (d : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.divisionMixedExchangeCorrection d G π a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  unfold divisionMixedExchangeCorrection complexCrossContraction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, B := by
      apply Finset.sum_le_sum
      intro ij _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      · have h := hG π ij.1 ij.2 (fun k => cyclicDivision d (x k))
        simpa only [cyclicDivision_val, Int.natCast_ediv] using h
      · rw [norm_mul, norm_star, norm_mul, norm_star, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          ((mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)).trans (W.norm_eval _ _))).trans
          ((mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)).trans (W.norm_eval _ _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, pow_two]

theorem exists_divisionMixedExchangeCorrection_expansion (s d : ℕ) [NeZero d] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (W.divisionMixedExchangeCorrection d G π a b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_mixed_rational_division_equivalence s d
  obtain ⟨B, _, hdivision⟩ := NativeIntegerExpansion.exists_division_expansion d (s + 2) (by omega)
  obtain ⟨D, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + A) ^ A + (p + q + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (q + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) B
  have hF (i j : Fin W.outputDim) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) t
      (fun x => G π i j (fun k => x k / (d : ℤ)))) :=
    ⟨(Classical.choice (hdivision hq (Classical.choice (hG π i j)))).mono hBt⟩
  have H := hcontract (fun i j x => G π i j (fun k => x k / (d : ℤ))) ht
    ((hcompare W π).mono hAt) ((hcompare W (mixedSwapSample π)).mono hAt) hF a b
  have hcost : (t + D) ^ D ≤ (p + q + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨(Classical.choice H).mono hcost⟩

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

theorem exists_division_mixed_last_slots_equivalence (d D : ℕ) [NeZero D] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin (d + 2))) (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => (W.rationalDilation ((D : ℚ)⁻¹)).eval i (mixedSampledInput π x))
        (fun i x => (W.rationalDilation ((D : ℚ)⁻¹)).eval i
          (mixedSampledInput (mixedPermuteSample e π) x)) := by
  obtain ⟨A, _, hcompare⟩ := exists_mixed_rational_division_equivalence d D
  obtain ⟨B, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have heq : (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π (fun k => x k / (D : ℤ)))) =
      (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) (fun k => x k / (D : ℤ)))) := by
    funext i x
    symm
    change W.eval i (mixedReplicatedInput (x (π 0) / (D : ℤ)) (fun j => x (π (e j).succ) / (D : ℤ))) =
      W.eval i (mixedReplicatedInput (x (π 0) / (D : ℤ)) (fun j => x (π j.succ) / (D : ℤ)))
    exact W.mixed_permutation_eval hsymm e i (x (π 0) / (D : ℤ)) (fun j => x (π j.succ) / (D : ℤ))
  have F : NativeIntegerVectorEquivalence (d + 2) ((p + A) ^ A)
      (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π (fun k => x k / (D : ℤ))))
      (fun i x => (W.rationalDilation ((D : ℚ)⁻¹)).eval i
        (mixedSampledInput (mixedPermuteSample e π) x)) := by
    rw [heq]
    exact (hcompare W (mixedPermuteSample e π)).symm
  have H := htrans hu (hcompare W π) F (fun x => W.unit_eval _)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

theorem exists_division_mixed_tensor_last_slots_equivalence (d D n : ℕ) [NeZero D] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin (d + 2))) (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => ((W.rationalDilation ((D : ℚ)⁻¹)).tensorPower n).eval i (mixedSampledInput π x))
        (fun i x => ((W.rationalDilation ((D : ℚ)⁻¹)).tensorPower n).eval i (mixedSampledInput (mixedPermuteSample e π) x)) := by
  obtain ⟨A, _, hdivision⟩ := exists_division_mixed_last_slots_equivalence d D
  obtain ⟨B, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_power_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have H := htensor hu (hdivision W hsymm e π)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have E := H.mono hcost
  have hdim : (Fintype.card (Fin ((W.rationalDilation ((D : ℚ)⁻¹)).tensorPower n).outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [Fintype.card_fin]
    change ((W.outputDim ^ n : ℕ) : ℝ) ≤ _
    have h := E.left_dimension
    simp only [Fintype.card_fun, Fintype.card_fin] at h
    change ((W.outputDim ^ n : ℕ) : ℝ) ≤ _ at h
    exact h
  apply E.of_coordinate_maps _ _ (tensorIndexEquiv W.outputDim n).symm
    (tensorIndexEquiv W.outputDim n).symm _ _ hdim hdim (le_refl _)
  · intro i x
    exact (W.rationalDilation ((D : ℚ)⁻¹)).tensorPower_eval n i (mixedSampledInput π x)
  · intro i x
    exact (W.rationalDilation ((D : ℚ)⁻¹)).tensorPower_eval n i
      (mixedSampledInput (mixedPermuteSample e π) x)

theorem exists_mixed_root_last_slots_equivalence (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin (d + 2))) (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => W.mixedIntegrationRoot.eval i (mixedSampledInput π x))
        (fun i x => W.mixedIntegrationRoot.eval i (mixedSampledInput (mixedPermuteSample e π) x)) := by
  obtain ⟨C, hC, h⟩ := exists_division_mixed_tensor_last_slots_equivalence d (d + 3) ((d + 3) ^ (d + 2))
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  exact h W hsymm e π

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedTensorExchangeCorrection (n : ℕ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ℤ) : ℂ :=
  ∏ k : Fin n, G π ((tensorIndexEquiv W.outputDim n).symm a k)
    ((tensorIndexEquiv W.outputDim n).symm b k) x

theorem mixedTensorExchange_kernel (n : ℕ) (π : Fin (s + 3) → Fin 2)
    (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ℤ) :
    (W.tensorPower n).eval a (mixedSampledInput π x) *
        star ((W.tensorPower n).eval b (mixedSampledInput (mixedSwapSample π) x)) =
      ∏ k : Fin n, W.eval ((tensorIndexEquiv W.outputDim n).symm a k) (mixedSampledInput π x) *
        star (W.eval ((tensorIndexEquiv W.outputDim n).symm b k)
          (mixedSampledInput (mixedSwapSample π) x)) := by
  simp only [tensorPower_eval, star_prod, Finset.prod_mul_distrib]

theorem mixedTensorExchangeCorrection_norm (n : ℕ) {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ZMod N) :
    ‖W.mixedTensorExchangeCorrection n G π a b (fun k => ((x k).val : ℤ))‖ ≤ B ^ n := by
  rw [mixedTensorExchangeCorrection, norm_prod]
  calc
    _ ≤ ∏ _ : Fin n, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hG _ _ _ x)
    _ = _ := by simp

theorem mixedTensorExchangeCorrection_mean_error (n : ℕ) {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.tensorPower n).eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star ((W.tensorPower n).eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.mixedTensorExchangeCorrection n G π a b (fun k => ((x k).val : ℤ))‖) ≤ B ^ n * (n * ε) := by
  let i := (tensorIndexEquiv W.outputDim n).symm a
  let j := (tensorIndexEquiv W.outputDim n).symm b
  have h := mean_prod_error_le
    (fun k (x : Fin 2 → ZMod N) =>
      W.eval (i k) (mixedSampledInput π (fun l => ((x l).val : ℤ))) *
        star (W.eval (j k) (mixedSampledInput (mixedSwapSample π) (fun l => ((x l).val : ℤ)))))
    (fun k (x : Fin 2 → ZMod N) => G π (i k) (j k) (fun l => ((x l).val : ℤ))) hB
    (fun k x => (by
      rw [norm_mul, norm_star]
      exact ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
        (W.norm_eval _ _)).trans hB))
    (fun _ x => hG _ _ _ x) (fun k => herr π (i k) (j k))
  simpa only [Fintype.card_fin, mixedTensorExchange_kernel, mixedTensorExchangeCorrection, i, j] using h

theorem exists_mixedTensorExchangeCorrection_expansion (s n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((q + C) ^ C)
        (W.mixedTensorExchangeCorrection n G π a b)) := by
  obtain ⟨C, hC, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  exact hprod _ hq (fun _ => hG _ _ _)

theorem dilationTensorMixedExchangeCorrection_mean_error (d n : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval a
            (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        (W.rationalDilation ((d : ℚ)⁻¹)).mixedTensorExchangeCorrection n
          (W.divisionMixedExchangeCorrection d G) π a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (2 * n) * (n * ((d : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hH (π : Fin (s + 3) → Fin 2) (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.divisionMixedExchangeCorrection d G π i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.divisionMixedExchangeCorrection_norm d G hG π i j x
  have h := (W.rationalDilation ((d : ℚ)⁻¹)).mixedTensorExchangeCorrection_mean_error n
    (W.divisionMixedExchangeCorrection d G) hB hH
    (W.divisionMixedExchangeCorrection_mean_error d G herr) π a b
  simpa only [← pow_mul] using h

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

def mixedCornerWeight {s : ℕ} (v : Fin (s + 3) → Fin 2) : ℕ := ∑ k, (v k).val

def mixedCornerSample {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  fun k => (v k).rev

def mixedCanonicalSample {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  fun k => if k.val < mixedCornerWeight v then 0 else 1

def mixedTailSortPermutation {s : ℕ} (v : Fin (s + 3) → Fin 2) : Equiv.Perm (Fin (s + 2)) :=
  Tuple.sort (fun j => mixedCornerSample v j.succ)

noncomputable def mixedHeadIndex {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 2) :=
  if h : ∃ j : Fin (s + 2), v j.succ = 1 then Classical.choose h else 0

noncomputable def mixedHeadPermutation {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    Equiv.Perm (Fin (s + 2)) := Equiv.swap 0 (mixedHeadIndex v)

noncomputable def mixedPreExchangeSample {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  mixedPermuteSample (mixedHeadPermutation v) (mixedCornerSample v)

noncomputable def mixedPostExchangePermutation {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    Equiv.Perm (Fin (s + 2)) :=
  Tuple.sort (fun j => mixedSwapSample (mixedPreExchangeSample v) j.succ)

def mixedExchangePermutation (s : ℕ) : Equiv.Perm (Fin (s + 3)) where
  toFun := mixedExchangeCoordinate (s + 1)
  invFun := mixedExchangeCoordinate (s + 1)
  left_inv := mixedExchangeCoordinate_involutive (s + 1)
  right_inv := mixedExchangeCoordinate_involutive (s + 1)

theorem mixedPermuteSample_eq_comp {s : ℕ} (e : Equiv.Perm (Fin (s + 2)))
    (π : Fin (s + 3) → Fin 2) : mixedPermuteSample e π = π ∘ zeroFixedPermutation e := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem mixedCornerSample_input {s : ℕ} (v : Fin (s + 3) → Fin 2) (x : Fin 2 → ℤ) :
    mixedDiagonalCorner v x = mixedSampledInput (mixedCornerSample v) x := rfl

theorem mixedCornerSample_zeroCount {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    binaryZeroCount (mixedCornerSample v) = mixedCornerWeight v := by
  rw [binaryZeroCount, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  change (if (v i).rev = 0 then 1 else 0) = (v i).val
  have H (b : Fin 2) : (if b.rev = 0 then 1 else 0) = b.val := by
    fin_cases b <;> decide
  exact H (v i)

theorem mixedCanonicalSample_eq_sorted {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    mixedCanonicalSample v = binarySorted (mixedCornerSample v) := by
  funext k
  rw [binarySorted_threshold, mixedCornerSample_zeroCount]
  rfl

theorem mixedCanonicalSample_of_first_one {s : ℕ} (v : Fin (s + 3) → Fin 2) (h0 : v 0 = 1) :
    mixedCanonicalSample v = mixedPermuteSample (mixedTailSortPermutation v) (mixedCornerSample v) := by
  rw [mixedCanonicalSample_eq_sorted, mixedPermuteSample_eq_comp]
  exact binarySorted_tail _ (by change (v 0).rev = 0; rw [h0]; rfl)

theorem mixedCorner_exists_tail_one {s : ℕ} (v : MixedNonconstantCorner s) (h0 : v.val 0 = 0) :
    ∃ j : Fin (s + 2), v.val j.succ = 1 := by
  classical
  by_contra h
  apply v.property
  funext j
  refine Fin.cases h0 (fun j => ?_) j
  exact binary_eq_zero_of_ne_one _ (fun hj => h ⟨j, hj⟩)

theorem mixedHeadIndex_one {s : ℕ} (v : MixedNonconstantCorner s) (h0 : v.val 0 = 0) :
    v.val (mixedHeadIndex v.val).succ = 1 := by
  have h := mixedCorner_exists_tail_one v h0
  simp only [mixedHeadIndex, dif_pos h]
  exact Classical.choose_spec h

theorem mixedPreExchangeSample_one {s : ℕ} (v : MixedNonconstantCorner s) (h0 : v.val 0 = 0) :
    mixedPreExchangeSample v.val 1 = 0 := by
  change (v.val ((Equiv.swap 0 (mixedHeadIndex v.val)) 0).succ).rev = 0
  rw [Equiv.swap_apply_left, mixedHeadIndex_one v h0]
  rfl

theorem mixedCanonicalSample_of_first_zero {s : ℕ} (v : MixedNonconstantCorner s)
    (h0 : v.val 0 = 0) :
    mixedCanonicalSample v.val = mixedPermuteSample (mixedPostExchangePermutation v.val)
      (mixedSwapSample (mixedPreExchangeSample v.val)) := by
  calc
    mixedCanonicalSample v.val = binarySorted (mixedCornerSample v.val) :=
      mixedCanonicalSample_eq_sorted _
    _ = binarySorted (mixedPreExchangeSample v.val) := by
      rw [mixedPreExchangeSample, mixedPermuteSample_eq_comp, binarySorted_comp]
    _ = binarySorted (mixedSwapSample (mixedPreExchangeSample v.val)) := by
      exact (binarySorted_comp (mixedPreExchangeSample v.val) (mixedExchangePermutation s)).symm
    _ = _ := by
      rw [mixedPermuteSample_eq_comp]
      exact binarySorted_tail _ (mixedPreExchangeSample_one v h0)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRootExchangeCorrection
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  (W.rationalDilation (((s + 3 : ℕ) : ℚ)⁻¹)).mixedTensorExchangeCorrection ((s + 3) ^ (s + 2)) (W.divisionMixedExchangeCorrection (s + 3) G)

theorem mixedRootExchangeCorrection_norm {N : ℕ} [NeZero N]
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.mixedIntegrationRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.mixedRootExchangeCorrection G π a b (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) := by
  have hH (π : Fin (s + 3) → Fin 2) (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.divisionMixedExchangeCorrection (s + 3) G π i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.divisionMixedExchangeCorrection_norm (s + 3) G hG π i j x
  simpa only [mixedRootExchangeCorrection, ← pow_mul] using
    (W.rationalDilation (((s + 3 : ℕ) : ℚ)⁻¹)).mixedTensorExchangeCorrection_norm ((s + 3) ^ (s + 2))
      (W.divisionMixedExchangeCorrection (s + 3) G) hH π a b x

theorem mixedRootExchangeCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.mixedIntegrationRoot.eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.mixedRootExchangeCorrection G π a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) *
        ((((s + 3) ^ (s + 2) : ℕ) : ℝ) *
          (((s + 3 : ℕ) : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)) := by
  exact W.dilationTensorMixedExchangeCorrection_mean_error
    (s + 3) ((s + 3) ^ (s + 2)) G hG herr π a b

theorem exists_mixedRootExchangeCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (W.mixedRootExchangeCorrection G π a b)) := by
  obtain ⟨A, _, hdivision⟩ := exists_divisionMixedExchangeCorrection_expansion s (s + 3)
  obtain ⟨B, _, htensor⟩ := exists_mixedTensorExchangeCorrection_expansion s ((s + 3) ^ (s + 2))
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := htensor (W.rationalDilation (((s + 3 : ℕ) : ℚ)⁻¹)) (by positivity : 0 ≤ (p + q + A) ^ A)
    (W.divisionMixedExchangeCorrection (s + 3) G) (hdivision W hq G hG) π a b
  have hcost : ((p + q + A) ^ A + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨E.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

def mixedCornerCount (s : ℕ) : ℕ := 2 ^ (s + 3) - 1

theorem mixedNonconstantCorner_card_eq (s : ℕ) :
    Fintype.card (MixedNonconstantCorner s) = mixedCornerCount s := mixedNonconstantCorner_card s

namespace NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRawCornerFactor (a b : MixedNonconstantCorner s → Fin W.outputDim)
    (v : MixedNonconstantCorner s) (x : Fin 2 → ℤ) : ℂ :=
  W.eval (a v) (mixedDiagonalCorner v.val x) *
    star (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) x))

theorem mixedRawCornerFactor_norm (a b : MixedNonconstantCorner s → Fin W.outputDim)
    (v : MixedNonconstantCorner s) (x : Fin 2 → ℤ) : ‖W.mixedRawCornerFactor a b v x‖ ≤ 1 := by
  rw [mixedRawCornerFactor, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

noncomputable def mixedCornerExchangeFactor
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : MixedNonconstantCorner s → Fin W.outputDim)
    (v : MixedNonconstantCorner s) (x : Fin 2 → ℤ) : ℂ :=
  if v.val 0 = 1 then W.mixedRawCornerFactor a b v x else
    complexCrossContraction
      (W.eval (a v) (mixedDiagonalCorner v.val x))
      (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) x))
      (fun i => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) x))
      (fun j => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val)) x))
      (fun i j => G (mixedPreExchangeSample v.val) i j x)

theorem mixedCornerExchangeFactor_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (v : MixedNonconstantCorner s)
    (x : Fin 2 → ZMod N) :
    ‖W.mixedCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hQ : 1 ≤ (W.outputDim : ℝ) ^ 2 * B :=
    hB.trans (le_mul_of_one_le_left (zero_le_one.trans hB) hd2)
  by_cases hv : v.val 0 = 1
  · rw [mixedCornerExchangeFactor, if_pos hv]
    exact (W.mixedRawCornerFactor_norm a b v _).trans hQ
  · rw [mixedCornerExchangeFactor, if_neg hv]
    have h := norm_complexCrossContraction_le_card
      (W.eval (a v) (mixedDiagonalCorner v.val (fun k => ((x k).val : ℤ))))
      (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) (fun k => ((x k).val : ℤ))))
      (fun i => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) (fun k => ((x k).val : ℤ))))
      (fun j => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val))
        (fun k => ((x k).val : ℤ))))
      (fun i j => G (mixedPreExchangeSample v.val) i j (fun k => ((x k).val : ℤ)))
      (W.norm_eval _ _) (W.norm_eval _ _) (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun i j => hG _ i j x)
    convert h using 1; first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

theorem mixedCornerExchangeFactor_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (v : MixedNonconstantCorner s) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedRawCornerFactor a b v (fun k => ((x k).val : ℤ)) -
        W.mixedCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ 2 * ε := by
  by_cases hv : v.val 0 = 1
  · simpa [mixedCornerExchangeFactor, hv] using mul_nonneg (sq_nonneg (W.outputDim : ℝ)) hε
  · simp only [mixedCornerExchangeFactor, if_neg hv, mixedRawCornerFactor]
    have h := mean_complexCrossContraction_error_le_card
      (fun x : Fin 2 → ZMod N => W.eval (a v) (mixedDiagonalCorner v.val (fun k => ((x k).val : ℤ))))
      (fun x => W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) (fun k => ((x k).val : ℤ))))
      (fun i x => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) (fun k => ((x k).val : ℤ))))
      (fun j x => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val))
        (fun k => ((x k).val : ℤ))))
      (fun i j x => G (mixedPreExchangeSample v.val) i j (fun k => ((x k).val : ℤ)))
      (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun _ => W.unit_eval _) (fun _ => W.unit_eval _)
      (fun _ _ => W.norm_eval _ _) (fun _ _ => W.norm_eval _ _) (herr (mixedPreExchangeSample v.val))
    convert h using 1; first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedCanonicalTensor (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.eval (a v) (mixedSampledInput (mixedCanonicalSample v.val) x))

theorem mixedCanonicalTensor_norm (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedCanonicalTensor a x‖ ≤ 1 := by
  rw [mixedCanonicalTensor, norm_star, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedNonconstantTensor_cross_symmetric
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedNonconstantTensor a x * star (W.mixedCanonicalTensor b x) =
      star (∏ v, W.mixedRawCornerFactor a b v x) := by
  simp only [mixedNonconstantTensor, mixedCanonicalTensor, mixedRawCornerFactor,
    Finset.prod_mul_distrib, star_prod, star_mul, star_star]
  ring

noncomputable def mixedCornerExchangeProduct
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.mixedCornerExchangeFactor G a b v x)

theorem mixedCornerExchangeProduct_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedNonconstantTensor a (fun k => ((x k).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedCornerExchangeProduct G a b (fun k => ((x k).val : ℤ))‖) ≤
      ((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) * ((mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * ε)) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hQ : 1 ≤ (W.outputDim : ℝ) ^ 2 * B :=
    hB.trans (le_mul_of_one_le_left (zero_le_one.trans hB) hd2)
  have h := mean_prod_error_le
    (fun v (x : Fin 2 → ZMod N) => W.mixedRawCornerFactor a b v (fun k => ((x k).val : ℤ)))
    (fun v (x : Fin 2 → ZMod N) => W.mixedCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))) hQ
    (fun v x => (W.mixedRawCornerFactor_norm a b v _).trans hQ)
    (fun v x => W.mixedCornerExchangeFactor_norm G hB hG a b v x)
    (fun v => W.mixedCornerExchangeFactor_mean_error G hε herr a b v)
  simpa only [W.mixedNonconstantTensor_cross_symmetric, mixedCornerExchangeProduct,
    ← star_sub, norm_star, mixedNonconstantCorner_card_eq] using h

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_corner_exchange_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ),
      0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin (s + 2))) (π : Fin (s + 3) → Fin 2), NativeIntegerVectorEquivalence (s + 2) r
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π x))
        (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) x))) →
      ∀ a b v, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((q + r + C) ^ C)
        (W.mixedCornerExchangeFactor G a b v)) := by
  obtain ⟨A, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b v
  let t := q + r
  have ht : 0 ≤ t := add_nonneg hq hr
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hrt : r ≤ t := by dsimp [t]; linarith
  have hsum : t + (t + A) ^ A ≤ (q + r + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget (q + r) (add_nonneg hq hr)
  have htC : t ≤ (q + r + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hAC : (t + A) ^ A ≤ (q + r + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  by_cases hv : v.val 0 = 1
  · have hcanon := mixedCanonicalSample_of_first_one v.val hv
    obtain ⟨F⟩ := ((hperm (mixedTailSortPermutation v.val)
      (mixedCornerSample v.val)).mono hrt).expansion (a v) (b v)
    have heq : (fun x => W.eval (a v) (mixedSampledInput (mixedCornerSample v.val) x) *
        star (W.eval (b v) (mixedSampledInput
          (mixedPermuteSample (mixedTailSortPermutation v.val)
            (mixedCornerSample v.val)) x))) = W.mixedCornerExchangeFactor G a b v := by
      funext x
      simp only [mixedCornerExchangeFactor, if_pos hv, mixedRawCornerFactor,
        mixedCornerSample_input, hcanon]
    exact ⟨heq ▸ F.mono htC⟩
  · have hv0 := binary_eq_zero_of_ne_one (v.val 0) hv
    have hcanon := mixedCanonicalSample_of_first_zero v hv0
    have Eleft : NativeIntegerVectorEquivalence (s + 2) t
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedDiagonalCorner v.val x))
        (fun i x => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) x)) := by
      simpa only [mixedCornerSample_input, mixedPreExchangeSample] using
        (hperm (mixedHeadPermutation v.val) (mixedCornerSample v.val)).mono hrt
    have Eright : NativeIntegerVectorEquivalence (s + 2) t
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput (mixedCanonicalSample v.val) x))
        (fun i x => W.eval i (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val)) x)) := by
      rw [hcanon]
      exact ((hperm (mixedPostExchangePermutation v.val)
        (mixedSwapSample (mixedPreExchangeSample v.val))).mono hrt).symm
    have H := hcontract (fun i j x => G (mixedPreExchangeSample v.val) i j x) ht Eleft Eright
      (fun i j => ⟨(Classical.choice (hG _ i j)).mono hqt⟩) (a v) (b v)
    have heq : (fun x => complexCrossContraction
        (W.eval (a v) (mixedDiagonalCorner v.val x))
        (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) x))
        (fun i => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) x))
        (fun j => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val)) x))
        (fun i j => G (mixedPreExchangeSample v.val) i j x)) = W.mixedCornerExchangeFactor G a b v := by
      funext x
      simp only [mixedCornerExchangeFactor, if_neg hv]
    exact ⟨heq ▸ (Classical.choice H).mono hAC⟩

theorem exists_mixed_corner_product_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ),
      0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin (s + 2))) (π : Fin (s + 3) → Fin 2), NativeIntegerVectorEquivalence (s + 2) r
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π x))
        (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) x))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((q + r + C) ^ C)
        (W.mixedCornerExchangeProduct G a b)) := by
  obtain ⟨A, _, hfactor⟩ := exists_mixed_corner_exchange_expansion s
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget (mixedCornerCount s)
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  let e : Fin (mixedCornerCount s) ≃ MixedNonconstantCorner s := (Fintype.equivFinOfCardEq (mixedNonconstantCorner_card_eq s)).symm
  obtain ⟨F⟩ := hprod (fun k => W.mixedCornerExchangeFactor G a b (e k))
    (by positivity : 0 ≤ (q + r + A) ^ A)
    (fun k => hfactor W G hq hr hG hperm a b (e k))
  have hcost : ((q + r + A) ^ A + B) ^ B ≤ (q + r + C) ^ C := by
    simpa [X, T, Polynomial.eval₂_pow] using hbudget (q + r) (add_nonneg hq hr)
  have heq : (fun x => star (∏ k : Fin (mixedCornerCount s), W.mixedCornerExchangeFactor G a b (e k) x)) =
      W.mixedCornerExchangeProduct G a b := by
    funext x
    exact congrArg star (e.prod_comp (fun v => W.mixedCornerExchangeFactor G a b v x))
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedPermutedDiagonalCorrection
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (b : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
    (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
      W.mixedCornerExchangeProduct G c b x

theorem mixedPermutedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π a b (x : Fin 2 → ZMod N), ‖G π a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (hε : 0 ≤ ε)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim) (b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (mixedCornerCount s) * (((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) * ((mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * ε))) := by
  have hid (x : Fin 2 → ℤ) :
      W.mixedDiagonalDerivative a x * star (W.mixedCanonicalTensor b x) =
        ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
          (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
            (W.mixedNonconstantTensor c x * star (W.mixedCanonicalTensor b x)) := by
    calc
      _ = ∑ c, ((W.mixedDiagonalDerivative a x * star (W.mixedCanonicalTensor b x)) *
          star (W.mixedNonconstantTensor c x)) * W.mixedNonconstantTensor c x :=
        complex_unit_vector_resolution _ (W.mixedNonconstantTensor_unit x) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        ring
  have hpoint (x : Fin 2 → ZMod N) :
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
        ‖W.mixedNonconstantTensor c (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          W.mixedCornerExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ := by
    rw [hid, mixedPermutedDiagonalCorrection, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c _
    rw [← mul_sub, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (W.mixedDiagonalDerivative_norm _ _)).trans (W.mixedNonconstantTensor_norm _ _)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
        ‖W.mixedNonconstantTensor c (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          W.mixedCornerExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ c : MixedNonconstantCorner s → Fin W.outputDim, 𝔼 x : Fin 2 → ZMod N,
        ‖W.mixedNonconstantTensor c (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          W.mixedCornerExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : MixedNonconstantCorner s → Fin W.outputDim,
        ((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) * ((mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * ε)) :=
      Finset.sum_le_sum (fun c _ => W.mixedCornerExchangeProduct_mean_error G hB hε hG herr c b)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        mixedNonconstantCorner_card_eq, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

theorem exists_mixed_permuted_diagonal_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ), 0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin (s + 2))) (π : Fin (s + 3) → Fin 2), NativeIntegerVectorEquivalence (s + 2) r
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π x))
        (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) x))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + r + C) ^ C)
        (W.mixedPermutedDiagonalCorrection G a b)) := by
  obtain ⟨A, _, hderivative⟩ := exists_mixed_diagonal_derivative_equivalence s
  obtain ⟨B, _, hseven⟩ := exists_mixed_corner_product_expansion s
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D + Polynomial.C (mixedCornerCount s) * X)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + r + A) ^ A + (p + q + r + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (q + r + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hterm (c : MixedNonconstantCorner s → Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((t + D) ^ D)
        (fun x => (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
          W.mixedCornerExchangeProduct G c b x)) := by
    exact hmul ht (Classical.choice (((hderivative W).mono hAt).expansion a c))
      ((Classical.choice (hseven W G hq hr hG hperm c b)).mono hBt)
  have hdim : (Fintype.card (MixedNonconstantCorner s → Fin W.outputDim) : ℝ) ≤ Real.exp ((mixedCornerCount s) * p) := by
    simp only [Fintype.card_fun, mixedNonconstantCorner_card_eq, Fintype.card_fin, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound (mixedCornerCount s)).trans_eq
      (Real.exp_nat_mul p (mixedCornerCount s)).symm
  have hcoeff : (∑ _ : MixedNonconstantCorner s → Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp ((mixedCornerCount s) * p) := by
    simpa using hdim
  have H := NativeIntegerExpansion.weightedSum (fun c => Classical.choice (hterm c))
    (fun _ => 1) (by positivity : 0 ≤ (mixedCornerCount s) * p) hdim hcoeff
  have hcost : (t + D) ^ D + (mixedCornerCount s) * p ≤ (p + q + r + C) ^ C := by
    have hb : (t + D) ^ D + (mixedCornerCount s) * (p + q + r) ≤ (p + q + r + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q + r) (by positivity)
    have hmono : (mixedCornerCount s : ℝ) * p ≤ (mixedCornerCount s : ℝ) * (p + q + r) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    linarith
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + r + C) ^ C)
    (fun x => ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
      (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
        W.mixedCornerExchangeProduct G c b x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRootCornerCorrection
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.mixedIntegrationRoot.mixedPermutedDiagonalCorrection (W.mixedRootExchangeCorrection G)

theorem mixedRootCornerCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedDiagonalDerivative a (fun k => ((x k).val : ℤ)) *
          star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedRootCornerCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.mixedIntegrationRoot.outputDim : ℝ) ^ mixedCornerCount s *
        (((W.mixedIntegrationRoot.outputDim : ℝ) ^ 2 *
            (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2)))) ^ mixedCornerCount s *
          ((mixedCornerCount s : ℝ) * ((W.mixedIntegrationRoot.outputDim : ℝ) ^ 2 *
            ((W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) *
              ((((s + 3) ^ (s + 2) : ℕ) : ℝ) *
                (((s + 3 : ℕ) : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)))))) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd (2 * ((s + 3) ^ (s + 2)))
  exact W.mixedIntegrationRoot.mixedPermutedDiagonalCorrection_mean_error
    (W.mixedRootExchangeCorrection G) hB (W.mixedRootExchangeCorrection_norm G hG)
    (by positivity) (W.mixedRootExchangeCorrection_mean_error G hG herr) a b

theorem exists_mixedRootCornerCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (s + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (s + 2)) a).symm j)) = W.eval i x) →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (W.mixedRootCornerCorrection G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_mixedRootExchangeCorrection_expansion s
  obtain ⟨B, _, hperm⟩ := exists_mixed_root_last_slots_equivalence s
  obtain ⟨D, _, hdiagonal⟩ := exists_mixed_permuted_diagonal_expansion s
  let n := (s + 3) ^ (s + 2)
  let X : Polynomial ℕ := Polynomial.X
  let T := Polynomial.C (n + 1) * (X + 1) + (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hdiagonal W.mixedIntegrationRoot (W.mixedRootExchangeCorrection G)
    (by positivity : 0 ≤ (p + q + A) ^ A) (by positivity : 0 ≤ (p + B) ^ B)
    (hroot W hq G hG) (hperm W hsymm) a b
  have hcost : (tensorPowerBudget n p + (p + q + A) ^ A + (p + B) ^ B + D) ^ D ≤
      (p + q + C) ^ C := by
    have hmono : (p + B) ^ B ≤ (p + q + B) ^ B :=
      pow_le_pow_left₀ (by positivity) (by linarith) B
    have hbase : tensorPowerBudget n p ≤ (n + 1 : ℝ) * (p + q + 1) := by
      unfold tensorPowerBudget
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hbound : ((n + 1 : ℝ) * (p + q + 1) + (p + q + A) ^ A + (p + q + B) ^ B + D) ^ D ≤
        (p + q + C) ^ C := by
      simpa [X, T, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
    apply le_trans _ hbound
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    linarith
  exact ⟨E.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

def mixedRootTensorExponent (s : ℕ) : ℕ := (s + 3) ^ (s + 2)

def mixedRootCornerExponent (s : ℕ) : ℕ :=
  5 * mixedRootTensorExponent s * mixedCornerCount s + 4 * mixedRootTensorExponent s + 2

def mixedRootCornerCoefficient (s : ℕ) : ℕ :=
  mixedCornerCount s * mixedRootTensorExponent s * (s + 3) ^ 2

theorem root_corner_loss_identity (D : ℝ) (n m q : ℕ) (ε : ℝ) :
    (D ^ n) ^ m * (((D ^ n) ^ 2 * D ^ (2 * n)) ^ m *
      ((m : ℝ) * ((D ^ n) ^ 2 * (D ^ (2 * n) *
        ((n : ℝ) * ((q : ℝ) ^ 2 * D ^ 2 * ε)))))) =
      ((m * n * q ^ 2 : ℕ) : ℝ) * D ^ (5 * n * m + 4 * n + 2) * ε := by
  have hp0 : (D ^ n) ^ m = D ^ (n * m) := (pow_mul D n m).symm
  have hp1 : ((D ^ n) ^ 2 * D ^ (2 * n)) ^ m = D ^ ((n * 2 + 2 * n) * m) := by
    simp only [← pow_mul, ← pow_add]
  have hp2 : (D ^ n) ^ 2 = D ^ (n * 2) := (pow_mul D n 2).symm
  have hp : D ^ (n * m) * D ^ ((n * 2 + 2 * n) * m) * D ^ (n * 2) * D ^ (2 * n) * D ^ 2 =
      D ^ (5 * n * m + 4 * n + 2) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hp0, hp1, hp2]
  calc
    _ = ((m : ℝ) * n * (q : ℝ) ^ 2) *
        (D ^ (n * m) * D ^ ((n * 2 + 2 * n) * m) * D ^ (n * 2) * D ^ (2 * n) * D ^ 2) * ε := by ring
    _ = _ := by rw [hp]; simp only [Nat.cast_mul, Nat.cast_pow]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedIntegrationRoot_outputDim :
    W.mixedIntegrationRoot.outputDim = W.outputDim ^ mixedRootTensorExponent s := rfl

theorem mixedRootCornerCorrection_mean_error_power {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedDiagonalDerivative a (fun k => ((x k).val : ℤ)) *
          star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedRootCornerCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      (mixedRootCornerCoefficient s : ℝ) * (W.outputDim : ℝ) ^ mixedRootCornerExponent s * ε := by
  have H := W.mixedRootCornerCorrection_mean_error G hε hG herr a b
  apply H.trans_eq
  rw [W.mixedIntegrationRoot_outputDim, Nat.cast_pow]
  exact root_corner_loss_identity (W.outputDim : ℝ) (mixedRootTensorExponent s) (mixedCornerCount s) (s + 3) ε

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct Pointwise

structure NativeCyclicModel (degree N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  norm : test.normBound ≤ 1
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = test.evalCyclic N (fun _ => x)

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

noncomputable def NativeCyclicModel.smul {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (F : NativeCyclicModel degree N p f) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NativeCyclicModel degree N p (c • f) where
  L := F.L
  dim := F.dim
  model := F.model
  test := F.test.scaleComplex c
  norm := (F.test.scaleComplex_norm hc).trans F.norm
  complexity := F.test.scaleComplex_complexity hc F.complexity
  eval x := by
    change c * f x = c * F.test.evalCyclic N (fun _ => x)
    rw [F.eval x]

def nativeCyclicFunctions (degree N : ℕ) [NeZero N] (p : ℝ) : Set (ZMod N → ℂ) :=
  {f | Nonempty (NativeCyclicModel degree N p f)}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def CyclicNativeInverse (s C : ℕ) : Prop :=
  ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → ∀ f : ZMod N → ℂ,
    (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 1) f →
    ∃ g ∈ nativeCyclicFunctions s N ((p + C) ^ C),
      Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x, f x * star (g x)‖

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeCommonDerivativeModels (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  geometry : model.GeometryComplexityLE p
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  test : ZMod N → model.Niltest (fun _ : Unit => 1)
  norm : ∀ h, (test h).normBound ≤ 1
  complexity : ∀ h, (test h).ComplexityLE p
  common_observable : ∀ h k, (test h).observable = (test k).observable
  correlation : ∀ h ∈ shifts, Real.exp (-p) ≤
    ‖𝔼 x, multiplicativeDerivative f h x * star ((test h).evalCyclic N (fun _ => x))‖

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

def NativeModelDetector (degree N : ℕ) [NeZero N] (p : ℝ)
    (X : Seminorm ℂ (ZMod N → ℂ)) (K M beta tau : ℝ) : Prop :=
  ∀ psi : ZMod N → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
    ∃ f ∈ nativeCyclicFunctions degree N p, beta ≤ ‖𝔼 x, psi x * star (f x)‖

def NativeTwoSiteModelingData (degree N : ℕ) [NeZero N]
    (p₁ p₂ K₁ K₂ beta₁ beta₂ eta : ℝ)
    (X₁ : Seminorm ℂ (ZMod N → ℂ))
    (X₂ : (ZMod N → ℂ) → Seminorm ℂ (ZMod N → ℂ)) (a b : ZMod N → ℂ) : Prop :=
  let tau₁ := eta / 4
  let tau₂ := eta * beta₁ / 8
  let length₁ := 1 + 4 * K₁ ^ 2 / (beta₁ ^ 2 * tau₁ ^ 2)
  let length₂ := 1 + 4 * K₂ ^ 2 / (beta₂ ^ 2 * tau₂ ^ 2)
  ∃ (n : ℕ) (_ : 0 < n) (f : Fin n → ZMod N → ℂ)
    (F : ∀ i, NativeCyclicModel degree N p₁ (f i))
    (c : Fin n → ℂ) (ea : ZMod N → ℂ)
    (m : Fin n → ℕ) (_ : ∀ i, 0 < m i)
    (g : ∀ i, Fin (m i) → ZMod N → ℂ)
    (G : ∀ i j, NativeCyclicModel degree N p₂ (g i j))
    (d : ∀ i, Fin (m i) → ℂ) (eb : Fin n → ZMod N → ℂ),
    (∀ x, a x = (∑ i, c i * (F i).test.evalCyclic N (fun _ => x)) + ea x) ∧
    (∀ i x, b x = (∑ j, d i j * (G i j).test.evalCyclic N (fun _ => x)) + eb i x) ∧
    (∑ i, ‖c i‖) ≤ 2 / beta₁ ∧ (∀ i, (∑ j, ‖d i j‖) ≤ 2 / beta₂) ∧
    X₁ ea + ∑ i, ‖c i‖ * X₂ (f i) (eb i) ≤ eta ∧
    (n : ℝ) ≤ length₁ ∧ (∀ i, (m i : ℝ) ≤ length₂) ∧
    (Fintype.card (Σ i, Fin (m i)) : ℝ) ≤ length₁ * length₂

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

noncomputable def NativeCommonDerivativeModels.mono {s N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} (B : NativeCommonDerivativeModels s N p f) (hpq : p ≤ q) :
    NativeCommonDerivativeModels s N q f :=
  { B with
    geometry := B.geometry.mono B.model hpq
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans B.density
    complexity := fun h => (B.complexity h).mono hpq
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (B.correlation h hh) }

theorem exists_normalized_native_common_models (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ},
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → (B : NativeCommonDerivativeModels s N p f) →
      ∃ R : NativeCommonDerivativeModels s N ((p + C) ^ C) f,
        ∀ h, R.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
          (R.test h).orbit = 1 := by
  obtain ⟨a, _, hnormalize⟩ := RationalFilteredNilmanifold.exists_normalized_common_correlators s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro N _ p f hp hf B
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨H, S, _, hH, hdense, hS, hsame, hcorr⟩ :=
    hnormalize B.model B.test B.shifts B.nonempty hp B.geometry B.complexity
      (fun h _ => B.norm h) (fun h x => multiplicativeDerivative f h x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h x) B.correlation
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + (p + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)
      _ = Real.exp (-((p + a) ^ a)) * (Real.exp (-p) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((p + a) ^ a)) * B.shifts.card :=
        mul_le_mul_of_nonneg_left B.density (Real.exp_nonneg _)
      _ ≤ _ := hdense
  let R : NativeCommonDerivativeModels s N ((p + C) ^ C) f := {
    L := B.L
    dim := B.dim
    model := B.model
    geometry := B.geometry.mono B.model hpC
    shifts := H
    nonempty := hH
    density := hfinaldensity
    test := S
    norm := fun h => (hS h).1
    complexity := fun h => (hS h).2.2.1.mono hqC
    common_observable := hsame
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh) }
  exact ⟨R, fun h => (hS h).2.2.2⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem cyclicNativeInverse_one : CyclicNativeInverse 1 2 := by
  intro N _ p hp f hf hG
  obtain ⟨χ, hχ⟩ := exists_large_fourier_of_gowers_two f hf
  obtain ⟨T, hTn, hTc, hTeval⟩ := exists_cyclic_character_niltest χ
  have h12 : (12 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have h2p : 2 * p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hcorr : Real.exp (-(2 * p)) ≤ ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ ≤ gowersNorm 2 f ^ 2 := pow_le_pow_left₀ (Real.exp_nonneg _) hG 2
      _ ≤ _ := hχ
  let F : NativeCyclicModel 1 N ((p + 2) ^ 2) (fun x => χ x) := {
    L := RationalTorus.Algebra 1
    dim := 1
    model := RationalTorus.nilmanifold 1
    test := T
    norm := hTn
    complexity := hTc.mono h12
    eval := fun x => (hTeval x).symm }
  exact ⟨fun x => χ x, ⟨F⟩, (Real.exp_le_exp.mpr (neg_le_neg h2p)).trans hcorr⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem mean_norm_le_fourier_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) : (𝔼 x, ‖f x‖) ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ := by
  have hpoint (x : G) : ‖f x‖ ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = ‖∑ χ : AddChar G ℂ, finiteFourierCoeff f χ * χ x‖ := by rw [finiteFourier_inversion]
      _ ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ * χ x‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, AddChar.norm_apply, mul_one]
  exact (Finset.expect_le_expect (fun x _ => hpoint x)).trans_eq (Fintype.expect_const _)

theorem exists_quadratic_small_modulus_correlation {N : ℕ} [NeZero N] {p q : ℝ}
    (hN : (N : ℝ) ≤ Real.exp q) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hGowers : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ g ∈ nativeCyclicFunctions 2 N 211,
      Real.exp (-(8 * p + q)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  have hmass : Real.exp (-(8 * p)) ≤ ∑ χ : AddChar (ZMod N) ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ 8 := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ gowersNorm 3 f ^ 8 := pow_le_pow_left₀ (Real.exp_nonneg _) hGowers 8
      _ ≤ 𝔼 n, ‖f n‖ := by simpa using gowersNorm_pow_le_mean_norm 2 f hf
      _ ≤ _ := mean_norm_le_fourier_sum f
  obtain ⟨χ, hχ⟩ := exists_large_nonnegative_weighted_term
    (fun _ : AddChar (ZMod N) ℂ => (1 : ℝ)) (fun χ => ‖finiteFourierCoeff f χ‖)
    (fun _ => by norm_num) (fun _ => norm_nonneg _) (Real.exp_pos _) (Real.exp_pos q)
    (by simpa using hN) (by simpa only [one_mul] using hmass)
  have hcorr : Real.exp (-(8 * p + q)) ≤ ‖finiteFourierCoeff f χ‖ := by
    have heq : Real.exp (-(8 * p)) / Real.exp q = Real.exp (-(8 * p + q)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hχ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := exists_cyclic_character_niltest χ
  let hdegree : 1 ≤ 2 := by omega
  refine ⟨fun n => χ n, ⟨{
    L := RationalTorus.Algebra 1
    dim := 1
    model := (RationalTorus.nilmanifold 1).raiseStep hdegree
    test := T.raiseStep hdegree
    norm := hTnorm
    complexity := ?_
    eval := ?_ }⟩, hcorr⟩
  · have hh := T.raiseStep_complexity hdegree (by norm_num) hT
    convert hh using 1
    norm_num [raisedNiltestBudget]
  · intro n
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    exact (hTeval n).symm

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeVerticalDerivativeData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) where
  normalized : ∀ h, B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
    (B.test h).orbit = 1
  frequency : B.L →ₗ[ℚ] ℚ
  height : ∀ i, rationalLogHeight (frequency (B.model.basis i)) ≤ p
  vertical : ∀ h z, z ∈ B.model.filtration.realification.subgroup s → ∀ x,
    (B.test h).observable (z • x) =
      CircleFourier.character ((realifyFunctional frequency z.coord : ℝ) : CircleFourier.Circle) *
        (B.test h).observable x
  integral : ∀ z : B.model.RealGroup, z ∈ B.model.filtration.realification.subgroup s →
    z ∈ B.model.realLattice → ∃ n : ℤ, realifyFunctional frequency z.coord = n

noncomputable def NativeVerticalDerivativeData.mono {s N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {B : NativeCommonDerivativeModels s N p f}
    (V : NativeVerticalDerivativeData B) (hpq : p ≤ q) :
    NativeVerticalDerivativeData (B.mono hpq) where
  normalized := V.normalized
  frequency := V.frequency
  height i := (V.height i).trans hpq
  vertical := V.vertical
  integral := V.integral

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansionSpec
namespace OAI

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  (B : PositiveShiftBasis.{u} s N q a J) {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))
  (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
  (R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1))
  (anchor : ZMod N) (H : Finset (ZMod N)) (p : ℝ)

structure CommonFactorization where
  weight : ∀ i, Fin (B.anchoredDimension d e i) → ℕ
  adapted : ∀ i k, (B.anchoredFactors D E i).filtration.layer k =
    Submodule.span ℚ ((B.anchoredFactors D E i).basis '' {j | k ≤ weight i j})
  subalgebra : LieSubalgebra ℚ (pi (B.anchoredFactors D E)).filtration.AssociatedGraded
  spanning : Fin (Fintype.card (Σ i, Fin (B.anchoredDimension d e i))) →
    (pi (B.anchoredFactors D E)).filtration.AssociatedGraded
  span_eq : Submodule.span ℚ (Set.range spanning) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule
    ((pi (B.anchoredFactors D E)).filtration.associatedGradedBasis (pi (B.anchoredFactors D E)).basis
      (productBasisWeight weight) (pi_layer_span (B.anchoredFactors D E) weight adapted))
    (productBasisWeight weight) subalgebra.toSubmodule
  height : ∀ i k, rationalLogHeight
    (((pi (B.anchoredFactors D E)).filtration.associatedGradedBasis (pi (B.anchoredFactors D E)).basis
      (productBasisWeight weight) (pi_layer_span (B.anchoredFactors D E) weight adapted)).repr (spanning i) k) ≤ p
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p
  shifts : Finset (ZMod N)
  shifts_sub : shifts ⊆ H
  shifts_nonempty : shifts.Nonempty
  shifts_large : Real.exp (-p) * N ≤ (shifts.card : ℝ)
  factors : ∀ h ∈ shifts, HasFixedProductOrbitFactors (B.anchoredFactors D E) none
    (fun i => (anchoredOptionReferenceData (B.test h) (B.test anchor) A (R h) i).orbit)
    (B.frequency h) (fun _ : Unit => (N : ℝ)) p denominator subalgebra
  frequency : ({h // h ∈ shifts} × Fin B.count) → ∀ i, B.anchoredLieSpace L M i →ₗ[ℚ] ℚ
  frequency_zero : ∀ j x,
    x ∈ (pi (B.anchoredFactors D E)).filtration.realGradedRefiltrationLayer subalgebra s →
      realifyFunctional (piFrequency (frequency j)) x = 0
  invariant : ∀ h ∈ shifts, ∀ z : B.model.RealGroup,
    z ∈ B.model.filtration.realification.subgroup s →
    (∀ j, realifyFunctional (frequency j none) z.coord = 0) → ∀ x,
      (B.test h).observable (z • x) = (B.test h).observable x

variable {B D E A R anchor H p}

def CommonFactorization.mono (F : B.CommonFactorization D E A R anchor H p) {p' : ℝ} (hpp' : p ≤ p') :
    B.CommonFactorization D E A R anchor H p' where
  weight := F.weight
  adapted := F.adapted
  subalgebra := F.subalgebra
  spanning := F.spanning
  span_eq := F.span_eq
  graded := F.graded
  height := fun i k => (F.height i k).trans hpp'
  denominator := F.denominator
  denominator_pos := F.denominator_pos
  denominator_bound := F.denominator_bound.trans (Real.exp_le_exp.mpr hpp')
  shifts := F.shifts
  shifts_sub := F.shifts_sub
  shifts_nonempty := F.shifts_nonempty
  shifts_large := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpp'))
    (Nat.cast_nonneg N)).trans F.shifts_large
  factors := fun h hh => (F.factors h hh).mono (B.anchoredFactors D E) none hpp'
    (fun _ => by exact_mod_cast NeZero.pos N)
  frequency := F.frequency
  frequency_zero := F.frequency_zero
  invariant := F.invariant

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  {B : PositiveShiftBasis.{u} s N q a J} {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  {D : ∀ j, RationalFilteredNilmanifold (L j) s (d j)}
  {E : ∀ j, RationalFilteredNilmanifold (M j) s (e j)}
  {A : ∀ j, (D j).Niltest (fun _ : Unit => 1)}
  {R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1)}
  {anchor : ZMod N} {H : Finset (ZMod N)} {p : ℝ}

def CommonFactorization.FactorFamily
    (F : B.CommonFactorization D E A R anchor H p) : Prop :=
    let T := B.anchoredFactors D E
    let g (h : ZMod N) : ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
      fun i => (anchoredOptionReferenceData (D := T) (B.test h) (B.test anchor) A (R h) i).orbit
    ∃ (κ : ZMod N → (pi T).RealGroup)
      (slow middle rat : ZMod N → ((pi T).filtration.realification.adaptedPolynomialFiltration
        (fun _ : Unit => 1)).Group),
      (∀ h ∈ F.shifts, κ h ∈ (pi T).realLattice) ∧
      (∀ h ∈ F.shifts, slow h * middle h * rat h *
        (pi T).filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) (κ h) =
          ⟨⟨(piRealOrbit (fun i => (T i).filtration)
            (g h)).log,
            (piRealOrbit (fun i => (T i).filtration)
            (g h)).property⟩⟩) ∧
      (∀ h ∈ F.shifts, (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
        (fun _ => (N : ℝ)) (Real.exp p) (slow h)) ∧
      (∀ h ∈ F.shifts, (pi T).filtration.PolynomialRationalGrid (pi T).basis (fun _ : Unit => 1)
        F.denominator (rat h)) ∧
      (∀ h ∈ F.shifts, coefficients
        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))) 0 = 0) ∧
      (∀ h ∈ F.shifts, ∀ α, coefficients
        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))) α ∈
          (pi T).filtration.realGradedRefiltrationLayer F.subalgebra (Finsupp.weight (fun _ : Unit => 1) α))

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  {B : PositiveShiftBasis.{u} s N q a J} {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  {D : ∀ j, RationalFilteredNilmanifold (L j) s (d j)}
  {E : ∀ j, RationalFilteredNilmanifold (M j) s (e j)}
  {A : ∀ j, (D j).Niltest (fun _ : Unit => 1)}
  {R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1)}
  {anchor : ZMod N} {H : Finset (ZMod N)} {p : ℝ}

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

def productExpansionBudget (p : ℝ) : ℝ := (2 * p + 4) ^ 2 + p + 2

def CommonRefilteredExpansionSpec (s r C : ℕ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q a J)
      {L M : Fin B.count → Type}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
      [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
      (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1) (e j))
      (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
      (R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1))
      (anchor : ZMod N) (H : Finset (ZMod N)) {p : ℝ}
      (F : B.CommonFactorization D E A R anchor H p),
      2 ≤ p → q ≤ p →
      (∀ j, (D j).GeometryComplexityLE p) → (∀ j, (E j).GeometryComplexityLE p) →
      let T := B.anchoredFactors D E
      let t := productExpansionBudget p
      ∃ U : RationalFilteredNilmanifold ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra)
          (s + 1) (finrank ℚ ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra)),
        U.filtration = (pi T).filtration.gradedRefiltration F.subalgebra ∧
        U.lattice = (pi T).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi T).filtration.gradedRefiltration F.subalgebra).lowerCentralSeries_eq_bot)
            ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra).incl) ∧
        U.GeometryComplexityLE ((t + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra) ⧸
                U.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = U.filtration.quotientTop ∧
            Q.lattice = U.lattice.map
              (U.filtration.quotientStepHom (U.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((t + C) ^ C) ∧
            (nativeRefilteredTarget T none F.subalgebra U Q).GeometryComplexityLE ((t + C) ^ C) ∧
            ∃ cost : ℝ, 0 ≤ cost ∧ cost ≤ (t + C) ^ C ∧
              RefilteredProductExpansionSpec T none F.subalgebra U Q t F.denominator r cost

end Erdos3.PositiveShiftBasis

end

end OAI

end


