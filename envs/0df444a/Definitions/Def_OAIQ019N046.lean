-- Prove2me | Definitions.Def_OAIQ019N046
-- name    : OAIQ019N046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:13:53.163445+00:00
-- url     : https://prove2.me/theorems/e58c5afe-d4cf-4493-9b2e-5565c165c0f8
-- title:
--   Definitions bundle OAIQ019N046 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 65 declarations of OpenAI's Lean: 23 definitions, 1 instance and 41 theorems. The definitions and types are `OAI.NuclearUltrapower.FiniteUnitaryRep.classSetoid`, `OAI.NuclearUltrapower.densityRoot`, `OAI.NuclearUltrapower.dualAction`, `OAI.NuclearUltrapower.finiteQuotientTuple`, `OAI.NuclearUltrapower.finiteTensorAction`, `OAI.NuclearUltrapower.finiteTensorAlpha`, `OAI.NuclearUltrapower.finiteTensorBeta`, `OAI.NuclearUltrapower.finiteTensorHilbert`, `OAI.NuclearUltrapower.hsConjugation`, `OAI.NuclearUltrapower.hsOperator`, `OAI.NuclearUltrapower.liftOperatorTensor`, `OAI.NuclearUltrapower.matchingTuple`, `OAI.NuclearUltrapower.matchingUnitary`, `OAI.NuclearUltrapower.reducedDensity`, `OAI.NuclearUltrapower.rightRepSequence`, `OAI.NuclearUltrapower.tensorAlpha`, `OAI.NuclearUltrapower.tensorBeta`, `OAI.NuclearUltrapower.tensorInclusion`, `OAI.NuclearUltrapower.tensorLeftSequence`, `OAI.NuclearUltrapower.tensorOperatorL`, `OAI.NuclearUltrapower.tensorProjection`, `OAI.NuclearUltrapower.tensorUnitaryAction`, `OAI.NuclearUltrapower.tupleRepresentation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_FiniteInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/FiniteInduction.lean), [`NuclearUltrapower_HilbertSchmidt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertSchmidt.lean), [`NuclearUltrapower_HilbertTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertTensor.lean), [`NuclearUltrapower_InducedApproximation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InducedApproximation.lean), [`NuclearUltrapower_NuclearFiniteness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/NuclearFiniteness.lean), [`NuclearUltrapower_SpatialGap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SpatialGap.lean), [`NuclearUltrapower_TensorMatching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/TensorMatching.lean).
--
--   **Imports.** It imports the published bundle `Def_NuclearUltrapower`; the bundle `OAIQ019N045` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ019N047`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N045

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertTensor
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower

section TensorOperators
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The elementary tensor bound, including unequal varying dimensions. -/
theorem completedTensorMap_norm_le (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    ‖completedTensorMap U V‖ ≤ ‖U‖ * ‖V‖ := by
  rw [completedTensorMap, completed_norm]
  exact TensorProduct.norm_mapL_le _ _

end TensorOperators
end NuclearUltrapower

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertSchmidt
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End

namespace NuclearUltrapower

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Matrix coefficient identity, valid without any countability restriction. -/
theorem tensorOperator_inner (z : K ⊗[ℂ] StrongDual ℂ K) (v y : K) :
    ⟪y, tensorOperator z v⟫_ℂ = ⟪y ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ K v, z⟫_ℂ := by
  induction z using OAI.tensorInductionOn with
  | tmul x f => simp [mul_comm]
  | add z w hz hw =>
      simp only [map_add, add_apply, inner_add_right, hz, hw]
      simp [TensorProduct.inner_def]

/-- The operator norm is bounded by the Hilbert tensor (Hilbert--Schmidt) norm. -/
theorem tensorOperator_norm_le (z : K ⊗[ℂ] StrongDual ℂ K) :
    ‖tensorOperator z‖ ≤ ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have h := norm_inner_le_norm (𝕜 := ℂ)
    (tensorOperator z v ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ K v) z
  rw [← tensorOperator_inner, inner_self_eq_norm_sq_to_K] at h
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm,
    TensorProduct.norm_tmul, LinearIsometryEquiv.norm_map] at h
  by_cases hn : ‖tensorOperator z v‖ = 0
  · rw [hn]; positivity
  · have hp : 0 < ‖tensorOperator z v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    apply (mul_le_mul_iff_right₀ hp).mp
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h

def tensorOperatorL : K ⊗[ℂ] StrongDual ℂ K →L[ℂ] (K →L[ℂ] K) := by
  refine LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := K ⊗[ℂ] StrongDual ℂ K) (F := K →L[ℂ] K)
    (tensorOperator (K := K)) 1 ?_
  intro z
  change ‖tensorOperator z‖ ≤ 1 * ‖z‖
  rw [one_mul]
  exact tensorOperator_norm_le (K := K) z

/-- Faithful operator realization of the Hilbert--Schmidt completion. -/
def hsOperator : HilbertSchmidt K →L[ℂ] (K →L[ℂ] K) :=
  (tensorOperatorL (K := K)).extend UniformSpace.Completion.toComplL

@[simp] theorem hsOperator_coe (z : K ⊗[ℂ] StrongDual ℂ K) :
    hsOperator (z : HilbertSchmidt K) = tensorOperator z := by
  exact ContinuousLinearMap.extend_eq (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := K ⊗[ℂ] StrongDual ℂ K) (Eₗ := HilbertSchmidt K) (F := K →L[ℂ] K)
    (tensorOperatorL (K := K))
    (e := UniformSpace.Completion.toComplL) UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) z

@[simp] theorem hsOperator_tmul (x v : K) (f : StrongDual ℂ K) :
    hsOperator ((x ⊗ₜ[ℂ] f : K ⊗[ℂ] StrongDual ℂ K) : HilbertSchmidt K) v = f v • x := by
  rw [hsOperator_coe, tensorOperator_tmul]

/-- Matrix coefficients of the completed operator realization. -/
theorem hsOperator_inner (z : HilbertSchmidt K) (v y : K) :
    ⟪y, hsOperator z v⟫_ℂ =
      ⟪((y ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ K v : K ⊗[ℂ] StrongDual ℂ K) :
        HilbertSchmidt K), z⟫_ℂ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact continuous_const.inner (𝕜 := ℂ) ((hsOperator (K := K)).continuous.clm_apply continuous_const)
      · exact continuous_const.inner (𝕜 := ℂ) (g := fun z : HilbertSchmidt K => z) continuous_id
  | ih z =>
      rw [hsOperator_coe, UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := K ⊗[ℂ] StrongDual ℂ K)]
      exact tensorOperator_inner z v y

/-- The operator realization loses no Hilbert--Schmidt vector. -/
theorem hsOperator_injective : Function.Injective (hsOperator (K := K)) := by
  apply (hsOperator (K := K)).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change hsOperator z = 0 at hz
  have hp (x : K) (f : StrongDual ℂ K) :
      ⟪((x ⊗ₜ[ℂ] f : K ⊗[ℂ] StrongDual ℂ K) : HilbertSchmidt K), z⟫_ℂ = 0 := by
    obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℂ K).surjective f
    rw [← hsOperator_inner, hz, zero_apply, inner_zero_right]
  have ha (w : K ⊗[ℂ] StrongDual ℂ K) :
      ⟪(w : HilbertSchmidt K), z⟫_ℂ = 0 := by
    induction w using OAI.tensorInductionOn with
    | tmul x f => exact hp x f
    | add x y hx hy =>
        rw [UniformSpace.Completion.coe_add, inner_add_left (𝕜 := ℂ) (E := HilbertSchmidt K), hx, hy, add_zero]
  have hall (w : HilbertSchmidt K) : ⟪w, z⟫_ℂ = 0 := by
    induction w using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (continuous_id.inner (𝕜 := ℂ) (E := HilbertSchmidt K)
        (g := fun _ : HilbertSchmidt K => z) continuous_const) continuous_const
    | ih w => exact ha w
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hall z)

/-- Conjugation is unitary for the Hilbert--Schmidt norm. -/
def hsConjugation (u : K ≃ₗᵢ[ℂ] K) : HilbertSchmidt K ≃ₗᵢ[ℂ] HilbertSchmidt K :=
  completionUnitary (E := K ⊗[ℂ] StrongDual ℂ K) (F := K ⊗[ℂ] StrongDual ℂ K)
    (TensorProduct.congrIsometry u (dualUnitary u))

@[simp] theorem hsConjugation_coe (u : K ≃ₗᵢ[ℂ] K) (z : K ⊗[ℂ] StrongDual ℂ K) :
    hsConjugation u (z : HilbertSchmidt K) =
      ((TensorProduct.congrIsometry u (dualUnitary u) z : K ⊗[ℂ] StrongDual ℂ K) :
        HilbertSchmidt K) := completionUnitary_coe _ z

/-- The tensor unitary acts by actual operator conjugation. -/
theorem hsOperator_conjugation (u : K ≃ₗᵢ[ℂ] K) (z : HilbertSchmidt K) :
    hsOperator (hsConjugation u z) =
      (u : K →L[ℂ] K) * hsOperator z * (u.symm : K →L[ℂ] K) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (hsOperator (K := K)).continuous.comp (hsConjugation u).continuous
      · exact (continuous_const.mul (hsOperator (K := K)).continuous).mul continuous_const
  | ih z =>
      rw [hsConjugation_coe, hsOperator_coe, hsOperator_coe]
      induction z using OAI.tensorInductionOn with
      | tmul x f => ext v; simp
      | add x y hx hy => simp only [map_add, hx, hy, mul_add, add_mul]

variable {Γ : Type*} [Group Γ]

@[simp] theorem hsConjugation_one : hsConjugation (1 : K ≃ₗᵢ[ℂ] K) = 1 := by
  ext z
  apply hsOperator_injective
  rw [hsOperator_conjugation]
  change (1 : K →L[ℂ] K) * hsOperator z * 1 = hsOperator z
  simp

@[simp] theorem hsConjugation_mul (u v : K ≃ₗᵢ[ℂ] K) :
    hsConjugation (u * v) = hsConjugation u * hsConjugation v := by
  ext z
  apply hsOperator_injective
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, hsOperator_conjugation]
  change (u : K →L[ℂ] K) * (v : K →L[ℂ] K) * hsOperator z *
      ((v.symm : K →L[ℂ] K) * (u.symm : K →L[ℂ] K)) = _
  simp only [mul_assoc]

end NuclearUltrapower

noncomputable section
open scoped CStarAlgebra

namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

@[simp] theorem tensorOperator_finiteOperatorTensor [FiniteDimensional ℂ K]
    (T : K →L[ℂ] K) : tensorOperator (finiteOperatorTensor T) = T := by
  classical
  ext x
  simp only [finiteOperatorTensor, map_sum, sum_apply, tensorOperator_tmul,
    InnerProductSpace.toDual_apply_apply]
  simpa only [map_sum, map_smul, OrthonormalBasis.repr_apply_apply] using
    congrArg T ((stdOrthonormalBasis ℂ K).sum_repr x)

/-- The Hilbert--Schmidt inner product equals the unnormalized operator trace. -/
theorem finiteOperatorTensor_inner [FiniteDimensional ℂ K]
    (T U : K →L[ℂ] K) :
    ⟪finiteOperatorTensor T, finiteOperatorTensor U⟫_ℂ =
      LinearMap.trace ℂ K ((star T * U).toLinearMap) := by
  classical
  rw [finiteOperatorTensor, sum_inner (𝕜 := ℂ) (E := K ⊗[ℂ] StrongDual ℂ K)]
  simp_rw [← tensorOperator_inner, tensorOperator_finiteOperatorTensor]
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ K)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (ContinuousLinearMap.adjoint_inner_right T _ _).symm

/-- All finite-dimensional operators have their actual Hilbert--Schmidt norm. -/
theorem finiteOperatorTensor_norm_sq [FiniteDimensional ℂ K] (T : K →L[ℂ] K) :
    ‖finiteOperatorTensor T‖ ^ 2 =
      (LinearMap.trace ℂ K ((star T * T).toLinearMap)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (finiteOperatorTensor T), finiteOperatorTensor_inner]
  rfl

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Tensorial inclusion of finite-rank operators along a Hilbert-space isometry. -/
def liftOperatorTensor (f : F →ₗᵢ[ℂ] K) [FiniteDimensional ℂ F] (T : F →L[ℂ] F) :
    K ⊗[ℂ] StrongDual ℂ K :=
  TensorProduct.mapIsometry f (dualIsometry f) (finiteOperatorTensor T)

@[simp] theorem liftOperatorTensor_norm (f : F →ₗᵢ[ℂ] K) [FiniteDimensional ℂ F]
    (T : F →L[ℂ] F) : ‖liftOperatorTensor f T‖ = ‖finiteOperatorTensor T‖ :=
  (TensorProduct.mapIsometry f (dualIsometry f)).norm_map _

/-- This inclusion is the usual compression along an isometric embedding. -/
theorem tensorOperator_liftOperatorTensor (f : F →ₗᵢ[ℂ] K) [FiniteDimensional ℂ F]
    (T : F →L[ℂ] F) :
    tensorOperator (liftOperatorTensor f T) =
      f.toContinuousLinearMap ∘L T ∘L f.toContinuousLinearMap.adjoint := by
  classical
  ext x
  simp only [liftOperatorTensor, finiteOperatorTensor, map_sum,
    TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
    sum_apply, tensorOperator_tmul]
  change (∑ i, dualIsometry f (InnerProductSpace.toDual ℂ F (stdOrthonormalBasis ℂ F i)) x •
    f (T (stdOrthonormalBasis ℂ F i))) = f (T (f.toContinuousLinearMap.adjoint x))
  simp only [dualIsometry_toDual, InnerProductSpace.toDual_apply_apply]
  have he (v : F) : ⟪f v, x⟫_ℂ = ⟪v, f.toContinuousLinearMap.adjoint x⟫_ℂ :=
    (ContinuousLinearMap.adjoint_inner_right f.toContinuousLinearMap v x).symm
  simp_rw [he]
  change (∑ i, ⟪stdOrthonormalBasis ℂ F i, f.toContinuousLinearMap.adjoint x⟫_ℂ •
    f (T (stdOrthonormalBasis ℂ F i))) = f (T (f.toContinuousLinearMap.adjoint x))
  simpa only [map_sum, map_smul, OrthonormalBasis.repr_apply_apply] using
    congrArg (fun y => f (T y)) ((stdOrthonormalBasis ℂ F).sum_repr
      (f.toContinuousLinearMap.adjoint x))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace K] in
@[simp] theorem crossOperator_tmul_rankOne (x : E) (y : K) :
    crossOperator (x ⊗ₜ[ℂ] y) =
      InnerProductSpace.rankOne ℂ y (InnerProductSpace.toDual ℂ E x) := by
  ext f
  simp

/-- The finite-rank reduced density; independent of any chosen tensor expansion. -/
def reducedDensity (z : E ⊗[ℂ] K) : K →L[ℂ] K :=
  crossOperator z ∘L (crossOperator z).adjoint

theorem reducedDensity_nonneg (z : E ⊗[ℂ] K) : 0 ≤ reducedDensity z :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_self_comp_adjoint _)

/-- The polarized partial-trace formula, before completion. -/
theorem trace_crossOperator [FiniteDimensional ℂ K] (z w : E ⊗[ℂ] K) (C : K →L[ℂ] K) :
    LinearMap.trace ℂ K ((C ∘L crossOperator z ∘L (crossOperator w).adjoint).toLinearMap) =
      ⟪w, TensorProduct.mapL (ContinuousLinearMap.id ℂ E) C z⟫_ℂ := by
  induction z using OAI.tensorInductionOn with
  | tmul x y =>
      induction w using OAI.tensorInductionOn with
      | tmul v t =>
          simp only [crossOperator_tmul_rankOne, InnerProductSpace.adjoint_rankOne,
            InnerProductSpace.comp_rankOne,
            InnerProductSpace.trace_rankOne, TensorProduct.mapL_tmul,
            ContinuousLinearMap.id_apply, TensorProduct.inner_tmul]
          simp only [InnerProductSpace.rankOne_apply, dual_inner_toDual,
            InnerProductSpace.toDual_apply_apply, map_smul, inner_smul_right]
      | add w₁ w₂ h₁ h₂ =>
          simp only [map_add, ContinuousLinearMap.comp_add, ContinuousLinearMap.toLinearMap_add,
            inner_add_left, h₁, h₂]
  | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.toLinearMap_add, inner_add_right, h₁, h₂]

/-- The reduced-density characterization by its trace. -/
theorem trace_reducedDensity [FiniteDimensional ℂ K] (z : E ⊗[ℂ] K) (C : K →L[ℂ] K) :
    LinearMap.trace ℂ K ((C * reducedDensity z).toLinearMap) =
      ⟪z, TensorProduct.mapL (ContinuousLinearMap.id ℂ E) C z⟫_ℂ :=
  trace_crossOperator z z C

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

omit [CompleteSpace K] [CompleteSpace F] in
/-- Naturality of the rectangular operator under arbitrary isometric embeddings. -/
theorem crossOperator_mapIsometry (g : E →ₗᵢ[ℂ] E') (f : F →ₗᵢ[ℂ] K) (z : E ⊗[ℂ] F) :
    crossOperator (TensorProduct.mapIsometry g f z) =
      f.toContinuousLinearMap ∘L crossOperator z ∘L (dualIsometry g).toContinuousLinearMap.adjoint := by
  induction z using OAI.tensorInductionOn with
  | tmul x y =>
      simp only [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul]
      change crossOperator (g x ⊗ₜ[ℂ] f y) = _
      rw [crossOperator_tmul_rankOne, crossOperator_tmul_rankOne,
        InnerProductSpace.rankOne_comp, ContinuousLinearMap.adjoint_adjoint,
        InnerProductSpace.comp_rankOne]
      change InnerProductSpace.rankOne ℂ (f y) (InnerProductSpace.toDual ℂ E' (g x)) =
        InnerProductSpace.rankOne ℂ (f y) (dualIsometry g (InnerProductSpace.toDual ℂ E x))
      rw [dualIsometry_toDual]
  | add z w hz hw =>
      simp only [map_add, hz, hw, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]

/-- Partial trace discards an isometry on the first tensor factor. -/
theorem reducedDensity_mapIsometry (g : E →ₗᵢ[ℂ] E') (f : F →ₗᵢ[ℂ] K) (z : E ⊗[ℂ] F) :
    reducedDensity (TensorProduct.mapIsometry g f z) = operatorLift f (reducedDensity z) := by
  simp only [reducedDensity, crossOperator_mapIsometry, operatorLift,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hg (y : StrongDual ℂ E) :
      (dualIsometry g).toContinuousLinearMap.adjoint (dualIsometry g y) = y :=
    congrArg (fun T : StrongDual ℂ E →L[ℂ] StrongDual ℂ E => T y)
      (dualIsometry g).adjoint_comp_self
  ext x
  change f (crossOperator z ((dualIsometry g).toContinuousLinearMap.adjoint
      (dualIsometry g ((crossOperator z).adjoint (f.toContinuousLinearMap.adjoint x))))) =
    f (crossOperator z ((crossOperator z).adjoint (f.toContinuousLinearMap.adjoint x)))
  rw [hg]

/-- Finite-dimensional density trace equals the vector's squared norm. -/
theorem trace_reducedDensity_self [FiniteDimensional ℂ K] (z : E ⊗[ℂ] K) :
    (LinearMap.trace ℂ K (reducedDensity z).toLinearMap).re = ‖z‖ ^ 2 := by
  have h := trace_reducedDensity z (ContinuousLinearMap.id ℂ K)
  rw [show (ContinuousLinearMap.id ℂ K) * reducedDensity z = reducedDensity z from one_mul _,
    TensorProduct.mapL_id_id, ContinuousLinearMap.id_apply] at h
  rw [h]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) z

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] theorem finiteOperatorTensor_sub [FiniteDimensional ℂ K] (T U : K →L[ℂ] K) :
    finiteOperatorTensor (T - U) = finiteOperatorTensor T - finiteOperatorTensor U := by
  classical
  simp only [finiteOperatorTensor, sub_apply, TensorProduct.sub_tmul,
    Finset.sum_sub_distrib]

/-- The root of a finite-rank density has squared Hilbert--Schmidt norm equal
exactly to the vector's squared Hilbert norm. -/
theorem finite_density_root_norm_sq [FiniteDimensional ℂ K] (z : E ⊗[ℂ] K) :
    ‖finiteOperatorTensor (CFC.sqrt (reducedDensity z))‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [finiteOperatorTensor_norm_sq, (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self _ (reducedDensity_nonneg z), trace_reducedDensity_self]

set_option maxHeartbeats 1000000 in
/-- Every algebraic tensor has a genuine Hilbert--Schmidt reduced-density root,
without any dimension or separability assumption on the ambient spaces. -/
theorem exists_density_root (z : E ⊗[ℂ] K) :
    ∃ a : HilbertSchmidt K, hsOperator a = CFC.sqrt (reducedDensity z) ∧ ‖a‖ = ‖z‖ := by
  obtain ⟨F, hF, hFz⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({z} : Set (E ⊗[ℂ] K)) (Set.finite_singleton z)
  let : FiniteDimensional ℂ F := hF
  obtain ⟨w, hw⟩ := hFz (Set.mem_singleton z)
  have hm : TensorProduct.mapIsometry ((LinearIsometry.id : E →ₗᵢ[ℂ] E)) F.subtypeₗᵢ w = z := hw
  have hd := reducedDensity_mapIsometry ((LinearIsometry.id : E →ₗᵢ[ℂ] E)) F.subtypeₗᵢ w
  rw [hm] at hd
  let t := liftOperatorTensor F.subtypeₗᵢ (CFC.sqrt (reducedDensity w))
  refine ⟨(t : HilbertSchmidt K), ?_, ?_⟩
  · rw [hsOperator_coe]
    change tensorOperator (liftOperatorTensor F.subtypeₗᵢ (CFC.sqrt (reducedDensity w))) = _
    rw [tensorOperator_liftOperatorTensor]
    change operatorLift F.subtypeₗᵢ (CFC.sqrt (reducedDensity w)) = _
    rw [operatorLift_sqrt F.subtypeₗᵢ (reducedDensity_nonneg w), ← hd]
  · rw [UniformSpace.Completion.norm_coe]
    change ‖liftOperatorTensor F.subtypeₗᵢ (CFC.sqrt (reducedDensity w))‖ = ‖z‖
    rw [liftOperatorTensor_norm]
    have hn : ‖w‖ = ‖z‖ := by
      rw [← hm, (TensorProduct.mapIsometry ((LinearIsometry.id : E →ₗᵢ[ℂ] E)) F.subtypeₗᵢ).norm_map]
    have hs := finite_density_root_norm_sq w
    rw [hn] at hs
    nlinarith [norm_nonneg (finiteOperatorTensor (CFC.sqrt (reducedDensity w))), norm_nonneg z]

/-- The unique Hilbert--Schmidt vector realizing the positive density root. -/
def densityRoot (z : E ⊗[ℂ] K) : HilbertSchmidt K := (exists_density_root z).choose

@[simp] theorem hsOperator_densityRoot (z : E ⊗[ℂ] K) :
    hsOperator (densityRoot z) = CFC.sqrt (reducedDensity z) :=
  (exists_density_root z).choose_spec.1

@[simp] theorem densityRoot_norm (z : E ⊗[ℂ] K) : ‖densityRoot z‖ = ‖z‖ :=
  (exists_density_root z).choose_spec.2

/-- Exact completed tensor action used in the source uniform spectral bound. -/
def tensorUnitaryAction {E K : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : E ≃ₗᵢ[ℂ] E) (v : K ≃ₗᵢ[ℂ] K) :
    HilbertTensor E K →L[ℂ] HilbertTensor E K :=
  (TensorProduct.mapL u.toContinuousLinearEquiv.toContinuousLinearMap
    v.toContinuousLinearEquiv.toContinuousLinearMap).completion

@[simp] theorem tensorUnitaryAction_coe {E K : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : E ≃ₗᵢ[ℂ] E) (v : K ≃ₗᵢ[ℂ] K) (z : E ⊗[ℂ] K) :
    tensorUnitaryAction u v (z : HilbertTensor E K) =
      (TensorProduct.congrIsometry u v z : HilbertTensor E K) := by
  rw [tensorUnitaryAction, ContinuousLinearMap.completion_apply_coe]
  simp only [TensorProduct.mapL_apply, TensorProduct.congrIsometry_apply]
  congr 1

end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
section Functor
variable {E E' E'' F F' F'' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup E''] [InnerProductSpace ℂ E'']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']
  [NormedAddCommGroup F''] [InnerProductSpace ℂ F'']

@[simp] theorem tensorMapBetween_adjoint [CompleteSpace E] [CompleteSpace E']
    [CompleteSpace F] [CompleteSpace F'] (U : E →L[ℂ] E') (V : F →L[ℂ] F') :
    tensorMapBetween U.adjoint V.adjoint = (tensorMapBetween U V).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    induction y using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y =>
      simp only [tensorMapBetween_coe, UniformSpace.Completion.inner_coe]
      induction x using OAI.tensorInductionOn with
      | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']
      | tmul a b =>
        induction y using OAI.tensorInductionOn with
        | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
        | tmul a' b' =>
          simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul]
          rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

end Functor
section Projection
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (W : Submodule ℂ F) [CompleteSpace W]

def tensorInclusion : TensorHilbert E W →ₗᵢ[ℂ] TensorHilbert E F :=
  tensorIsometry (LinearIsometry.id) W.subtypeₗᵢ

def tensorProjection : TensorHilbert E F →L[ℂ] TensorHilbert E W :=
  tensorMapBetween (1 : E →L[ℂ] E) W.orthogonalProjectionOnto

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem tensorInclusion_projection :
    (tensorInclusion (E := E) W).toContinuousLinearMap.comp (tensorProjection (E := E) W) =
      completedTensorMap (1 : E →L[ℂ] E) W.starProjection := by
  rw [tensorProjection, tensorInclusion, tensorIsometry_toCLM, ← tensorMapBetween_comp]
  rfl

end Projection
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SpatialGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
noncomputable section
open scoped TensorProduct
noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder

section TensorComplement
variable {Γ B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

@[simp] theorem pairedTensorUnitary_action (u : unitary (E →L[ℂ] E)) (v : unitary (F →L[ℂ] F)) :
    (pairedTensorUnitary u v : TensorHilbert E F →L[ℂ] TensorHilbert E F) =
      tensorUnitaryAction (Unitary.linearIsometryEquiv u) (Unitary.linearIsometryEquiv v) := by
  rw [pairedTensorUnitary_coe]; rfl

end TensorComplement

section SpatialGap
variable {Γ : Type u} [Group Γ] {B C : Type v} [CStarAlgebra B] [CStarAlgebra C]

def tupleRepresentation (q : Γ →* unitary C) (K : ComplexHilbert.{v})
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) : Γ →* (K ≃ₗᵢ[ℂ] K) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    ((Unitary.map (StarMonoidHom.ofClass σ)).toMonoidHom.comp q)

@[simp] theorem tupleRepresentation_apply (q : Γ →* unitary C) (K : ComplexHilbert.{v})
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (g : Γ) :
    tupleRepresentation q K σ g =
      Unitary.linearIsometryEquiv (Unitary.map (StarMonoidHom.ofClass σ) (q g)) := rfl

end SpatialGap
end NuclearUltrapower

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NuclearFiniteness
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal TensorProduct
namespace NuclearUltrapower

instance tensorHilbertNontrivial {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Nontrivial F] :
    Nontrivial (TensorHilbert E F) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine ⟨⟨(x ⊗ₜ[ℂ] y : E ⊗[ℂ] F), 0, ?_⟩⟩
  intro he
  have hn := congrArg norm he
  have hp : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  simp only [UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul, norm_zero] at hn
  linarith

section TensorCoordinateMaps
variable {ι : Type u} {E : Type v} {F : ι → Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
  [∀ i, CompleteSpace (F i)] [∀ i, Nontrivial (F i)]
  {B : Type*} [CStarAlgebra B] (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E))
  (ω : Ultrafilter ι)

/-- First tensor factor, represented uniformly at every coordinate. -/
def tensorLeftSequence : B →⋆ₐ[ℂ] VariableUltra.Seq (fun i => TensorHilbert E (F i) →L[ℂ] TensorHilbert E (F i)) where
  toFun b := ⟨fun _ => tensorLeftHom (ρ b), memℓp_infty ⟨‖b‖, by
    rintro _ ⟨i, rfl⟩
    change ‖completedTensorMap (ρ b) (1 : F i →L[ℂ] F i)‖ ≤ ‖b‖
    calc
      _ ≤ ‖ρ b‖ * ‖(1 : F i →L[ℂ] F i)‖ := completedTensorMap_norm_le _ _
      _ = ‖ρ b‖ := by rw [norm_one, mul_one]
      _ ≤ ‖b‖ := NonUnitalStarAlgHom.norm_apply_le ρ b⟩⟩
  map_zero' := by apply Subtype.ext; funext i; exact map_zero ((tensorLeftHom (F := F i)).comp ρ)
  map_one' := by apply Subtype.ext; funext i; exact map_one ((tensorLeftHom (F := F i)).comp ρ)
  map_add' b c := by apply Subtype.ext; funext i; exact map_add ((tensorLeftHom (F := F i)).comp ρ) b c
  map_mul' b c := by apply Subtype.ext; funext i; exact map_mul ((tensorLeftHom (F := F i)).comp ρ) b c
  commutes' c := by apply Subtype.ext; funext i; exact ((tensorLeftHom (F := F i)).comp ρ).commutes c
  map_star' b := by apply Subtype.ext; funext i; exact map_star ((tensorLeftHom (F := F i)).comp ρ) b

@[simp] theorem tensorLeftSequence_apply (b : B) (i : ι) :
    tensorLeftSequence (F := F) ρ b i = tensorLeftHom (ρ b) := rfl

def tensorAlpha : B →⋆ₐ[ℂ]
    (HilbertUltraproduct (fun i => TensorHilbert E (F i)) ω →L[ℂ]
      HilbertUltraproduct (fun i => TensorHilbert E (F i)) ω) :=
  (HilbertUltraproduct.unitalOperatorRep ω).comp (tensorLeftSequence ρ)

@[simp] theorem tensorAlpha_apply (b : B) :
    tensorAlpha (F := F) ρ ω b = HilbertUltraproduct.unitalOperatorRep ω
      (tensorLeftSequence (F := F) ρ b) := rfl

def tensorBeta : VariableUltra.Algebra (fun i => F i →L[ℂ] F i) ω →⋆ₐ[ℂ]
    (HilbertUltraproduct (fun i => TensorHilbert E (F i)) ω →L[ℂ]
      HilbertUltraproduct (fun i => TensorHilbert E (F i)) ω) :=
  VariableUltra.quotientHilbertRep ω (fun _ => tensorRightHom)

end TensorCoordinateMaps
end NuclearUltrapower
end
end

section
noncomputable section
universe u v
open Filter
open scoped InnerProductSpace TensorProduct Topology ENNReal ComplexOrder
namespace NuclearUltrapower
section NuclearFiniteness
variable {Γ : Type u} [Group Γ] {B : Type v} [CStarAlgebra B]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (ω : Ultrafilter ℕ)

/-- The actual quotient group tuple from the varying finite-dimensional family. -/
def finiteQuotientTuple : Γ →* unitary (VariableUltra.operatorQuotient (fun i => π i) ω) :=
  ((Unitary.map (VariableUltra.starAlgToStarMonoid (VariableUltra.mk _ ω))).toMonoidHom).comp
    (VariableUltra.representationSequence π)

@[simp] theorem tupleRepresentation_finite (K : ComplexHilbert.{v})
    (σ : VariableUltra.operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    tupleRepresentation (finiteQuotientTuple π ω) K σ =
      VariableUltra.quotientRepresentation π ω σ := rfl

/-- Coordinate second factors, before passing to either quotient. -/
def rightRepSequence (g : Γ) : VariableUltra.Seq
    (fun i => TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) :=
  VariableUltra.sequenceHom (fun i => tensorRightHom (E := E) (F := π i))
    (VariableUltra.representationSequence π g)

@[simp] theorem tensorBeta_finiteQuotient (g : Γ) :
    tensorBeta (E := E) (F := fun i => π i) ω (finiteQuotientTuple π ω g) =
      HilbertUltraproduct.unitalOperatorRep (E := fun i => TensorHilbert E (π i)) ω
        (rightRepSequence (E := E) π g) := by
  rfl

/-- Named bundled coordinates keep all tensor/Hilbert instances shared. -/
def finiteTensorHilbert : ComplexHilbert.{v} :=
  ⟨HilbertUltraproduct (fun i => TensorHilbert E (π i)) ω⟩

def finiteTensorAlpha : B →⋆ₐ[ℂ] (finiteTensorHilbert (E := E) π ω →L[ℂ]
    finiteTensorHilbert (E := E) π ω) := tensorAlpha (F := fun i => π i) ρ ω

def finiteTensorBeta : VariableUltra.operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ]
    (finiteTensorHilbert (E := E) π ω →L[ℂ] finiteTensorHilbert (E := E) π ω) :=
  tensorBeta (E := E) (F := fun i => π i) ω

def finiteTensorAction : VariableUltra.Seq
    (fun i => TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) →⋆ₐ[ℂ]
    (finiteTensorHilbert (E := E) π ω →L[ℂ] finiteTensorHilbert (E := E) π ω) :=
  HilbertUltraproduct.unitalOperatorRep ω

@[simp] theorem finiteTensorAlpha_val (b : B) :
    finiteTensorAlpha ρ π ω b = finiteTensorAction (E := E) π ω
      (tensorLeftSequence (F := fun i => π i) ρ b) := rfl

@[simp] theorem finiteTensorBeta_val (g : Γ) :
    finiteTensorBeta (E := E) π ω (finiteQuotientTuple π ω g) =
      finiteTensorAction (E := E) π ω (rightRepSequence (E := E) π g) := rfl

end NuclearFiniteness
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v
open scoped InnerProductSpace ComplexOrder TensorProduct
namespace NuclearUltrapower
section Matching
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

def matchingUnitary (π : FiniteUnitaryRep.{u,v} Γ) (g : Γ) :
    unitary (TensorHilbert E π →L[ℂ] TensorHilbert E π) :=
  pairedTensorUnitary (Unitary.map (VariableUltra.starAlgToStarMonoid ρ) (u g))
    (Unitary.linearIsometryEquiv.symm (π.action g))

def matchingTuple (π : FiniteUnitaryRep.{u,v} Γ) (g : Γ) :
    TensorHilbert E π ≃ₗᵢ[ℂ] TensorHilbert E π :=
  Unitary.linearIsometryEquiv (matchingUnitary ρ u π g)

omit [Nontrivial E] in
@[simp] theorem matchingUnitary_val (π : FiniteUnitaryRep.{u,v} Γ) (g : Γ) :
    (matchingUnitary ρ u π g : TensorHilbert E π →L[ℂ] TensorHilbert E π) =
      completedTensorMap (ρ (u g)) (π.action g : π →L[ℂ] π) := rfl

def FiniteUnitaryRep.classSetoid (Γ : Type u) [Group Γ] : Setoid (FiniteUnitaryRep.{u,v} Γ) where
  r := FiniteUnitaryRep.Equivalent
  iseqv := ⟨FiniteUnitaryRep.equivalent_refl, fun h => h.symm, fun h k => h.trans k⟩

end Matching
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InducedApproximation
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
universe u v
variable {Γ : Type u} [Group Γ]

section DualAction
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def dualAction (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) :
    Γ →* (StrongDual ℂ H ≃ₗᵢ[ℂ] StrongDual ℂ H) where
  toFun g := dualUnitary (ρ g)
  map_one' := by
    ext f : 1
    obtain ⟨x,rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective f
    rw [dualUnitary_toDual, map_one]
    rfl
  map_mul' g h := by
    ext f : 1
    obtain ⟨x,rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective f
    change dualUnitary (ρ (g*h)) (InnerProductSpace.toDual ℂ H x) =
      dualUnitary (ρ g) (dualUnitary (ρ h) (InnerProductSpace.toDual ℂ H x))
    rw [dualUnitary_toDual, dualUnitary_toDual, dualUnitary_toDual, map_mul]
    rfl

@[simp] theorem dualAction_toDual (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (g : Γ) (x : H) :
    dualAction ρ g (InnerProductSpace.toDual ℂ H x) =
      InnerProductSpace.toDual ℂ H (ρ g x) := dualUnitary_toDual _ _
end DualAction

end NuclearUltrapower
end
end

end OAI
end


