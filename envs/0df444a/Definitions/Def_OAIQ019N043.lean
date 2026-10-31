-- Prove2me | Definitions.Def_OAIQ019N043
-- name    : OAIQ019N043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:29:35.851304+00:00
-- url     : https://prove2.me/theorems/be35db4d-159f-4645-b8be-baec0c3799ef
-- title:
--   Definitions bundle OAIQ019N043 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 124 declarations of OpenAI's Lean: 110 definitions, 2 instances and 12 theorems. The definitions and types are `OAI.NuclearUltrapower.FullGroupModel.algebraicInclusion`, `OAI.NuclearUltrapower.FullGroupModel.generator`, `OAI.NuclearUltrapower.FullGroupModel.inclusion`, `OAI.NuclearUltrapower.FullGroupModel.modelMap`, `OAI.NuclearUltrapower.HilbertUltraproduct.approximateRepresentation`, `OAI.NuclearUltrapower.HilbertUltraproduct.preUnitary`, `OAI.NuclearUltrapower.HilbertUltraproduct.unitary`, `OAI.NuclearUltrapower.InjectiveInducedSpace`, `OAI.NuclearUltrapower.Matches`, `OAI.NuclearUltrapower.SOS.residualRow20`, `OAI.NuclearUltrapower.SOS.residualRow21`, `OAI.NuclearUltrapower.SOS.residualRow22`, `OAI.NuclearUltrapower.SOS.residualRow23`, `OAI.NuclearUltrapower.SOS.residualRow24`, `OAI.NuclearUltrapower.SOS.residualRow25`, `OAI.NuclearUltrapower.SOS.residualRow26`, `OAI.NuclearUltrapower.SOS.residualRow27`, `OAI.NuclearUltrapower.SOS.residualRow28`, `OAI.NuclearUltrapower.SOS.residualRow29`, `OAI.NuclearUltrapower.SOS.residualRow3`, `OAI.NuclearUltrapower.SOS.residualRow30`, `OAI.NuclearUltrapower.SOS.residualRow31`, `OAI.NuclearUltrapower.SOS.residualRow32`, `OAI.NuclearUltrapower.SOS.residualRow33`, `OAI.NuclearUltrapower.SOS.residualRow34`, `OAI.NuclearUltrapower.SOS.residualRow35`, `OAI.NuclearUltrapower.SOS.residualRow36`, `OAI.NuclearUltrapower.SOS.residualRow37`, `OAI.NuclearUltrapower.SOS.residualRow38`, `OAI.NuclearUltrapower.SOS.residualRow39`, `OAI.NuclearUltrapower.SOS.residualRow4`, `OAI.NuclearUltrapower.SOS.residualRow40`, `OAI.NuclearUltrapower.SOS.residualRow41`, `OAI.NuclearUltrapower.SOS.residualRow42`, `OAI.NuclearUltrapower.SOS.residualRow43`, `OAI.NuclearUltrapower.SOS.residualRow44`, `OAI.NuclearUltrapower.SOS.residualRow45`, `OAI.NuclearUltrapower.SOS.residualRow46`, `OAI.NuclearUltrapower.SOS.residualRow47`, `OAI.NuclearUltrapower.SOS.residualRow48` and 70 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_FullGroupAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/FullGroupAlgebra.lean), [`NuclearUltrapower_GroupObstruction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/GroupObstruction.lean), [`NuclearUltrapower_HilbertSchmidt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertSchmidt.lean), [`NuclearUltrapower_InducedApproximation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InducedApproximation.lean), [`NuclearUltrapower_InitialMatching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InitialMatching.lean), [`NuclearUltrapower_NuclearFiniteness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/NuclearFiniteness.lean), [`NuclearUltrapower_PullbackMatching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/PullbackMatching.lean), [`NuclearUltrapower_SOSResidual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSResidual.lean), [`NuclearUltrapower_Schur`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Schur.lean), [`NuclearUltrapower_SpatialGap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SpatialGap.lean), [`NuclearUltrapower_TensorMatching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/TensorMatching.lean).
--
--   **Imports.** It imports the published bundle `Def_NuclearUltrapower`; the bundles `OAIQ019N047` and `OAIQ019N041` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ019N044`; the statements `OAI.NuclearUltrapower.contradiction_of_initial_match`, `OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower`, `OAI.NuclearUltrapower.initial_match`, `OAI.NuclearUltrapower.injectiveInduced_invariant_tensor`, `OAI.NuclearUltrapower.matchClasses_finite`, `OAI.NuclearUltrapower.matched_vectors` and `OAI.NuclearUltrapower.uniform_predecessors`; the proofs of `OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing`, `OAI.NuclearUltrapower.contradiction_of_initial_match`, `OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower`, `OAI.NuclearUltrapower.initial_match`, `OAI.NuclearUltrapower.injectiveInduced_invariant_tensor`, `OAI.NuclearUltrapower.matchClasses_finite`, `OAI.NuclearUltrapower.matched_vectors` and `OAI.NuclearUltrapower.uniform_predecessors`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N047
import Definitions.Def_OAIQ019N041

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FullGroupAlgebra
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped MonoidAlgebra

noncomputable section
open UniformSpace

namespace NuclearUltrapower.FullGroupModel
open UniformSpace
open scoped MonoidAlgebra CStarAlgebra
open GroupStarAlgebra
variable (Γ : Type) [Group Γ]

instance instCStarAlgebraFull : CStarAlgebra (Full Γ) :=
  UniversalCompletion.cstarAlgebra GroupStarAlgebra.norm_mul_self_le

def algebraicInclusion : ℂ[Γ] →⋆ₐ[ℂ] Full Γ := UniversalCompletion.inclusion

/-- The canonical group generators are unitaries in the full completion. -/
def generator (g : Γ) : unitary (Full Γ) :=
  ⟨algebraicInclusion Γ (MonoidAlgebra.single g 1), by
    rw [Unitary.mem_iff]
    constructor
    · rw [← map_star, ← map_mul, GroupStarAlgebra.star_single]
      simp only [star_one, MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul,
        ← MonoidAlgebra.one_def, map_one]
    · rw [← map_star, ← map_mul, GroupStarAlgebra.star_single]
      simp only [star_one, MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul,
        ← MonoidAlgebra.one_def, map_one]⟩

def inclusion : Γ →* unitary (Full Γ) where
  toFun := generator Γ
  map_one' := by
    apply Subtype.ext
    change algebraicInclusion Γ (MonoidAlgebra.single 1 1) = 1
    exact map_one _
  map_mul' g h := by
    apply Subtype.ext
    change algebraicInclusion Γ (MonoidAlgebra.single (g*h) 1) =
      algebraicInclusion Γ (MonoidAlgebra.single g 1) * algebraicInclusion Γ (MonoidAlgebra.single h 1)
    rw [← map_mul, MonoidAlgebra.single_mul_single, one_mul]

@[simp] theorem inclusion_coe (g : Γ) :
    (inclusion Γ g : Full Γ) = algebraicInclusion Γ (MonoidAlgebra.single g 1) := rfl

/-- Extension to every model, not merely to Hilbert-space models. -/
def modelMap {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D) : Full Γ →⋆ₐ[ℂ] D :=
  UniversalCompletion.extend (evaluate ρ) (evaluate_continuous ρ)

@[simp] theorem modelMap_coe {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D) (x : ℂ[Γ]) :
    modelMap Γ ρ (algebraicInclusion Γ x) = evaluate ρ x :=
  UniversalCompletion.extend_coe _ _ _

@[simp] theorem modelMap_generator {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D) (g : Γ) :
    modelMap Γ ρ (inclusion Γ g) = (ρ g : D) := by
  rw [inclusion_coe, modelMap_coe, evaluate_single, one_smul]

instance instNontrivialFull : Nontrivial (Full Γ) := by
  apply nontrivial_of_ne (0 : Full Γ) 1
  intro h
  have := congrArg (modelMap Γ (1 : Γ →* unitary ℂ)) h
  exact zero_ne_one (by simpa only [map_zero, map_one] using this)

end NuclearUltrapower.FullGroupModel
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertSchmidt
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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

variable {Γ : Type*} [Group Γ]

/-- The conjugation representation on all Hilbert--Schmidt operators. -/
def hsRepresentation (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) :
    Γ →* (HilbertSchmidt K ≃ₗᵢ[ℂ] HilbertSchmidt K) where
  toFun g := hsConjugation (σ g)
  map_one' := by rw [map_one, hsConjugation_one]
  map_mul' g h := by rw [map_mul, hsConjugation_mul]

end NuclearUltrapower

noncomputable section
open scoped CStarAlgebra

namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] theorem liftOperatorTensor_sub [FiniteDimensional ℂ F]
    (f : F →ₗᵢ[ℂ] K) (T U : F →L[ℂ] F) :
    liftOperatorTensor f (T - U) = liftOperatorTensor f T - liftOperatorTensor f U := by
  simp only [liftOperatorTensor, finiteOperatorTensor_sub, map_sub]

end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Schur
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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
namespace NuclearUltrapower

open scoped TensorProduct
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {Γ : Type u} [Group Γ]

section MixedTensor
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- All matrix coefficients, using Lean's second-variable-linear inner product. -/
theorem mixedTensorOperator_inner (z : E ⊗[ℂ] StrongDual ℂ F) (v : F) (y : E) :
    ⟪y, mixedTensorOperator z v⟫_ℂ = ⟪y ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ F v, z⟫_ℂ := by
  induction z using OAI.tensorInductionOn with
  | tmul x f => simp [mul_comm]
  | add z w hz hw =>
      simp only [map_add, add_apply, inner_add_right, hz, hw]
      simp [TensorProduct.inner_def]

theorem mixedTensorOperator_injective : Function.Injective (mixedTensorOperator (E := E) (F := F)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change mixedTensorOperator z = 0 at hz
  have hp (x : E) (f : StrongDual ℂ F) : ⟪x ⊗ₜ[ℂ] f, z⟫_ℂ = 0 := by
    obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℂ F).surjective f
    rw [← mixedTensorOperator_inner, hz, zero_apply, inner_zero_right]
  have ha (w : E ⊗[ℂ] StrongDual ℂ F) : ⟪w, z⟫_ℂ = 0 := by
    induction w using OAI.tensorInductionOn with
    | tmul x f => exact hp x f
    | add x y hx hy => rw [inner_add_left (𝕜 := ℂ) (E := E ⊗[ℂ] StrongDual ℂ F), hx, hy, add_zero]
  exact (inner_self_eq_zero (𝕜 := ℂ) (E := E ⊗[ℂ] StrongDual ℂ F)).mp (ha z)

def tensorContragredientRep (ρ : Γ →* (E ≃ₗᵢ[ℂ] E)) (π : Γ →* (F ≃ₗᵢ[ℂ] F)) :
    Γ →* (E ⊗[ℂ] StrongDual ℂ F ≃ₗᵢ[ℂ] E ⊗[ℂ] StrongDual ℂ F) where
  toFun g := TensorProduct.congrIsometry (ρ g) (dualUnitary (π g))
  map_one' := by
    ext z
    induction z using OAI.tensorInductionOn with
    | tmul x f =>
      apply mixedTensorOperator_injective
      ext y
      simp
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  map_mul' g h := by
    ext z
    induction z using OAI.tensorInductionOn with
    | tmul x f =>
      apply mixedTensorOperator_injective
      ext y
      simp
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

end MixedTensor

end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SpatialGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
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

def spatialUnitaryTuple (H K : ComplexHilbert)
    (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (u : Γ → unitary B) (q : Γ → unitary C) :
    Γ → unitary (TensorHilbert H K →L[ℂ] TensorHilbert H K) := by
  let a : Γ → unitary (H →L[ℂ] H) := fun s => Unitary.map (StarMonoidHom.ofClass ρ) (u s)
  let b : Γ → unitary (K →L[ℂ] K) := fun s => Unitary.map (StarMonoidHom.ofClass σ) (q s)
  exact fun s => pairedTensorUnitary (a s) (b s)

end TensorComplement

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
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v
open Filter
open scoped InnerProductSpace TensorProduct Topology ENNReal ComplexOrder
namespace NuclearUltrapower
section ComplementEvaluation
variable {Γ B C D A : Type*} [CStarAlgebra B] [CStarAlgebra C] [CStarAlgebra D]
  [CStarAlgebra A]

@[simp] theorem map_complementPoly (f : A →⋆ₐ[ℂ] D) (S : Finset Γ) (z w : Γ → A) :
    f (complementPoly S z w) = complementPoly S (fun g => f (z g)) (fun g => f (w g)) := by
  simp only [complementPoly, map_add, map_smul, map_sum, map_one, map_mul, map_star]

end ComplementEvaluation
section NuclearFiniteness
variable {Γ : Type u} [Group Γ] {B : Type v} [CStarAlgebra B]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (ω : Ultrafilter ℕ)

/-- The complemented Laplacian as one uniformly bounded operator sequence. -/
def coordinateComplement (S : Finset Γ) (u : Γ → unitary B) : VariableUltra.Seq
    (fun i => TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) :=
  complementPoly S (fun g => tensorLeftSequence (F := fun i => π i) ρ (u g))
    (rightRepSequence (E := E) π)

end NuclearFiniteness
end NuclearUltrapower
end
end

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    (ω : Ultrafilter ι)

/-- Coordinate unitaries preserve the ultralimit seminorm. -/
def preUnitary (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    UltraPreHilbert E ω ≃ₗᵢ[ℂ] UltraPreHilbert E ω where
  toLinearMap := UltraPreHilbert.mapLinear ω (boundedUnitary U)
  invFun := UltraPreHilbert.mapLinear ω (boundedUnitary (fun i => (U i).symm))
  left_inv x := by
    apply Subtype.ext; funext i
    exact (U i).symm_apply_apply _
  right_inv x := by
    apply Subtype.ext; funext i
    exact (U i).apply_symm_apply _
  norm_map' x := by
    have h := UltraPreHilbert.norm_tendsto ω
      (UltraPreHilbert.mapLinear ω (boundedUnitary U) x)
    simp only [UltraPreHilbert.family_map, boundedUnitary_apply,
      LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.norm_map] at h
    exact tendsto_nhds_unique h (UltraPreHilbert.norm_tendsto ω x)

/-- Coordinate unitaries act unitarily on the completed Hilbert ultraproduct. -/
def unitary (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    HilbertUltraproduct E ω ≃ₗᵢ[ℂ] HilbertUltraproduct E ω :=
  (preUnitary ω U).toLinearEquiv.extendOfIsometry
    UniformSpace.Completion.toComplₗᵢ.toLinearMap UniformSpace.Completion.toComplₗᵢ.toLinearMap
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
    (fun x => by simp)

@[simp] theorem unitary_coe (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) (x : UltraPreHilbert E ω) :
    unitary ω U (x : HilbertUltraproduct E ω) =
      (preUnitary ω U x : HilbertUltraproduct E ω) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- Compatibility with the faithful operator realization. -/
theorem unitary_toContinuousLinearMap (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    (unitary ω U : HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω) =
      map ω (boundedUnitary U) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => rw [LinearIsometryEquiv.coe_coe'', unitary_coe, map_coe]; rfl

@[simp] theorem unitary_one :
    unitary ω (fun i => (1 : E i ≃ₗᵢ[ℂ] E i)) = 1 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [unitary_coe]
    change (preUnitary ω (fun i => (1 : E i ≃ₗᵢ[ℂ] E i)) x : HilbertUltraproduct E ω) = x
    rfl

@[simp] theorem unitary_mul (U V : ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    unitary ω (fun i => U i * V i) = unitary ω U * unitary ω V := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    change unitary ω (fun i => U i * V i) (x : HilbertUltraproduct E ω) =
      unitary ω U (unitary ω V x)
    rw [unitary_coe, unitary_coe, unitary_coe]
    rfl

/-- Operator-norm null changes in a family of unitaries do not change its
Hilbert-ultraproduct action. -/
theorem unitary_eq_of_tendsto (U V : ∀ i, E i ≃ₗᵢ[ℂ] E i)
    (h : Tendsto (fun i => ‖(U i : E i →L[ℂ] E i) - (V i : E i →L[ℂ] E i)‖)
      (ω : Filter ι) (𝓝 0)) : unitary ω U = unitary ω V := by
  have hz := (map_eq_zero_iff ω (boundedUnitary U - boundedUnitary V)).mpr h
  have hadd := map_add ω (boundedUnitary U - boundedUnitary V) (boundedUnitary V)
  rw [sub_add_cancel, hz, zero_add] at hadd
  ext x
  have he := congrArg (fun T : HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω => T x) hadd
  simpa only [← unitary_toContinuousLinearMap, LinearIsometryEquiv.coe_coe''] using he

/-- Pointwise asymptotic multiplicativity suffices. There is no hidden
intersection over all group relations, nor any dimension bound. -/
def approximateRepresentation {Γ : Type w} [Group Γ]
    (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) (ω : Filter ι) (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g * h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) (ω : Filter ι) (𝓝 0)) :
    Γ →* (HilbertUltraproduct E ω ≃ₗᵢ[ℂ] HilbertUltraproduct E ω) where
  toFun g := unitary ω (U g)
  map_one' := (unitary_eq_of_tendsto ω _ _ h1).trans (unitary_one ω)
  map_mul' g h := by
    change unitary ω (U (g * h)) = unitary ω (U g) * unitary ω (U h)
    have he := unitary_eq_of_tendsto ω (U (g * h))
      (fun i => U g i * U h i) (hmul g h)
    exact he.trans (unitary_mul ω (U g) (U h))

end HilbertUltraproduct
end NuclearUltrapower

end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
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

/-- Direct second-factor convention. Conjugating all irreducibles gives an
equivalent convention with the same quantification over representation classes. -/
def Matches (a : ℝ) (π : FiniteUnitaryRep.{u,v} Γ) : Prop :=
  ∃ x : TensorHilbert E π, ‖x‖ = 1 ∧ tupleEnergy S (matchingTuple ρ u π) x < a

def matchClasses (a : ℝ) : Set (RepClass (Γ := Γ)) :=
  {q | ∃ π : FiniteUnitaryRep.{u,v} Γ, π.Irreducible ∧ Matches ρ S u a π ∧
    Quotient.mk (FiniteUnitaryRep.classSetoid Γ) π = q}

end Matching
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InducedApproximation
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u
section InducedVectors
variable {Γ B E : Type u} [Group Γ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (H : Subgroup Γ) [Fintype (Γ ⧸ H)] (α : FiniteUnitaryRep.{u,u} H)
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → unitary B)

def inducedCoordinate (i : Γ ⧸ H) : α →ₗᵢ[ℂ] finiteInduced H α :=
  coordinateInclusion H i

/-- The fixed finite list of induced tensor coordinates. -/
def inductionTerm (i : Γ ⧸ H) : TensorHilbert E α →L[ℂ] TensorHilbert E (finiteInduced H α) :=
  tensorMapBetween (ρ (u (cosetRep H i))) (inducedCoordinate H α i).toContinuousLinearMap

def inductionSeed (η : TensorHilbert E α) : TensorHilbert E (finiteInduced H α) :=
  ∑ i : Γ ⧸ H, inductionTerm H α ρ u i η

end InducedVectors
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InitialMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u
section InitialMatch
variable {Γ A B E K : Type u} [Group Γ] [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (hρ : Function.Injective ρ)
  (S : Finset Γ) (ω : Ultrafilter ℕ)
  (φ : A →⋆ₐ[ℂ] VariableUltra.Algebra (fun _ : ℕ => B) ω) (hφ : Function.Injective φ)
  (w : Γ → A) (u : Γ → ℕ → unitary B)
  (hu : ∀ g, φ (w g) = VariableUltra.mk (fun _ : ℕ => B) ω
    (VariableUltra.unitarySequence (fun _ : ℕ => B) (u g)))
  (ψ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : Γ → K ≃ₗᵢ[ℂ] K)
  (hψ : ∀ g, ψ (w g) = (σ g : K →L[ℂ] K))
local instance instPartialOrder_solutions_3 : PartialOrder B := CStarAlgebra.spectralOrder B
local instance instPartialOrderAlgebraNat : PartialOrder (VariableUltra.Algebra (fun _ : ℕ => B) ω) :=
  CStarAlgebra.spectralOrder _
end InitialMatch
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_PullbackMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
universe u v w
section Range
variable {Γ : Type u} [Group Γ] (θ : Monoid.End Γ) (hθ : Function.Injective θ)

def rangeTwist (π : FiniteUnitaryRep.{u,u} Γ) : FiniteUnitaryRep.{u,u} θ.range :=
  π.comap (MonoidHom.ofInjective hθ).symm.toMonoidHom

end Range
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section Shift
variable {Γ Δ B E : Type u} [Group Γ] [Group Δ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (f : Γ →* Δ)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) (t : Δ)

def rangeTwistInclusion (π : FiniteUnitaryRep.{u,u} Γ) : π →ₗᵢ[ℂ] rangeTwist θ hθ π :=
  LinearIsometry.id

/-- Translation of a tensor vector by the stable-letter coordinate. -/
def shiftVector (π : FiniteUnitaryRep.{u,u} Γ) (b : unitary B) :
    TensorHilbert E π →ₗᵢ[ℂ] TensorHilbert E (rangeTwist θ hθ π) :=
  tensorIsometry (representedUnitary ρ b).toLinearIsometry (rangeTwistInclusion θ hθ π)

end Shift
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_GroupObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower
universe u v w
section InjectiveInduction
variable {Γ : Type u} {Δ : Type v} [Group Γ] [Group Δ]
  (f : Γ →* Δ) (hf : Function.Injective f) (π : FiniteUnitaryRep.{u,w} Γ)

/-- Induction along an honest subgroup inclusion; the index may be infinite. -/
abbrev InjectiveInducedSpace := lp (fun _ : Δ ⧸ f.range => π) 2

def injectiveInduced : Δ →* (InjectiveInducedSpace f π ≃ₗᵢ[ℂ] InjectiveInducedSpace f π) :=
  inducedUnitary f.range (π.action.comp (MonoidHom.ofInjective hf).symm.toMonoidHom)

end InjectiveInduction
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
def residualRow3 : Poly Mat3 := (basis.zip gramRow1).map (fun q => (matMul (matInv [0, 0, -1, 0, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow4 : Poly Mat3 := (basis.zip gramRow2).map (fun q => (matMul (matInv [0, 0, 1, 0, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow5 : Poly Mat3 := (basis.zip gramRow3).map (fun q => (matMul (matInv [0, 1, 0, -1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow6 : Poly Mat3 := (basis.zip gramRow4).map (fun q => (matMul (matInv [1, -2, 0, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow7 : Poly Mat3 := (basis.zip gramRow5).map (fun q => (matMul (matInv [1, -1, -1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow8 : Poly Mat3 := (basis.zip gramRow6).map (fun q => (matMul (matInv [1, -1, -1, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow9 : Poly Mat3 := (basis.zip gramRow7).map (fun q => (matMul (matInv [1, -1, -1, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow20 : Poly Mat3 := (basis.zip gramRow18).map (fun q => (matMul (matInv [1, -1, 0, 1, 0, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow21 : Poly Mat3 := (basis.zip gramRow19).map (fun q => (matMul (matInv [1, -1, 1, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow22 : Poly Mat3 := (basis.zip gramRow20).map (fun q => (matMul (matInv [1, -1, 1, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow23 : Poly Mat3 := (basis.zip gramRow21).map (fun q => (matMul (matInv [1, -1, 1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow24 : Poly Mat3 := (basis.zip gramRow22).map (fun q => (matMul (matInv [1, 0, -2, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow25 : Poly Mat3 := (basis.zip gramRow23).map (fun q => (matMul (matInv [1, 0, -1, -1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow26 : Poly Mat3 := (basis.zip gramRow24).map (fun q => (matMul (matInv [1, 0, -1, -1, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow27 : Poly Mat3 := (basis.zip gramRow25).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow28 : Poly Mat3 := (basis.zip gramRow26).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, -1, 0, 2]) q.1, -10*q.2))
def residualRow29 : Poly Mat3 := (basis.zip gramRow27).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow30 : Poly Mat3 := (basis.zip gramRow28).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow31 : Poly Mat3 := (basis.zip gramRow29).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow32 : Poly Mat3 := (basis.zip gramRow30).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 0, 1, 0, 0]) q.1, -10*q.2))
def residualRow33 : Poly Mat3 := (basis.zip gramRow31).map (fun q => (matMul (matInv [1, 0, -1, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow34 : Poly Mat3 := (basis.zip gramRow32).map (fun q => (matMul (matInv [1, 0, -1, 1, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow35 : Poly Mat3 := (basis.zip gramRow33).map (fun q => (matMul (matInv [1, 0, -1, 1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow36 : Poly Mat3 := (basis.zip gramRow34).map (fun q => (matMul (matInv [1, 0, 0, -2, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow37 : Poly Mat3 := (basis.zip gramRow35).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow38 : Poly Mat3 := (basis.zip gramRow36).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, -1, 1, 0, 1]) q.1, -10*q.2))
def residualRow39 : Poly Mat3 := (basis.zip gramRow37).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow40 : Poly Mat3 := (basis.zip gramRow38).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, -1, 1, 1]) q.1, -10*q.2))
def residualRow41 : Poly Mat3 := (basis.zip gramRow39).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow42 : Poly Mat3 := (basis.zip gramRow40).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow43 : Poly Mat3 := (basis.zip gramRow41).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow44 : Poly Mat3 := (basis.zip gramRow42).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 1, -1, 1]) q.1, -10*q.2))
def residualRow45 : Poly Mat3 := (basis.zip gramRow43).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow46 : Poly Mat3 := (basis.zip gramRow44).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 1, -1, 0, 1]) q.1, -10*q.2))
def residualRow47 : Poly Mat3 := (basis.zip gramRow45).map (fun q => (matMul (matInv [1, 0, 0, -1, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow48 : Poly Mat3 := (basis.zip gramRow46).map (fun q => (matMul (matInv [1, 0, 0, 0, 0, -1, 0, 1, 1]) q.1, -10*q.2))
def residualRow49 : Poly Mat3 := (basis.zip gramRow47).map (fun q => (matMul (matInv [1, 0, 0, 0, 0, 1, 0, -1, 1]) q.1, -10*q.2))
def residualRow50 : Poly Mat3 := (basis.zip gramRow48).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -2, 0, 0, 1]) q.1, -10*q.2))
def residualRow51 : Poly Mat3 := (basis.zip gramRow49).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, -1, 0, 1]) q.1, -10*q.2))
def residualRow52 : Poly Mat3 := (basis.zip gramRow50).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, 0, -1, 2]) q.1, -10*q.2))
def residualRow53 : Poly Mat3 := (basis.zip gramRow51).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow54 : Poly Mat3 := (basis.zip gramRow52).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, 0, 1, 0]) q.1, -10*q.2))
def residualRow55 : Poly Mat3 := (basis.zip gramRow53).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, -1, 1, 0, 1]) q.1, -10*q.2))
def residualRow56 : Poly Mat3 := (basis.zip gramRow54).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, -2, 0, 1]) q.1, -10*q.2))
def residualRow57 : Poly Mat3 := (basis.zip gramRow55).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, -1, -1, 1]) q.1, -10*q.2))
def residualRow58 : Poly Mat3 := (basis.zip gramRow56).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow59 : Poly Mat3 := (basis.zip gramRow57).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, -1, 1, 1]) q.1, -10*q.2))
def residualRow60 : Poly Mat3 := (basis.zip gramRow58).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, -2, 1]) q.1, -10*q.2))
def residualRow61 : Poly Mat3 := (basis.zip gramRow59).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow62 : Poly Mat3 := (basis.zip gramRow60).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow63 : Poly Mat3 := (basis.zip gramRow61).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow64 : Poly Mat3 := (basis.zip gramRow62).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 0, 2, 1]) q.1, -10*q.2))
def residualRow65 : Poly Mat3 := (basis.zip gramRow63).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 1, -1, 1]) q.1, -10*q.2))
def residualRow66 : Poly Mat3 := (basis.zip gramRow64).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow67 : Poly Mat3 := (basis.zip gramRow65).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 1, 1, 1]) q.1, -10*q.2))
def residualRow68 : Poly Mat3 := (basis.zip gramRow66).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 0, 2, 0, 1]) q.1, -10*q.2))
def residualRow69 : Poly Mat3 := (basis.zip gramRow67).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, -1, 0, 1]) q.1, -10*q.2))
def residualRow70 : Poly Mat3 := (basis.zip gramRow68).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, 0, -1, 0]) q.1, -10*q.2))
def residualRow71 : Poly Mat3 := (basis.zip gramRow69).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow72 : Poly Mat3 := (basis.zip gramRow70).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, 0, 1, 2]) q.1, -10*q.2))
def residualRow73 : Poly Mat3 := (basis.zip gramRow71).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 1, 1, 0, 1]) q.1, -10*q.2))
def residualRow74 : Poly Mat3 := (basis.zip gramRow72).map (fun q => (matMul (matInv [1, 0, 0, 0, 1, 2, 0, 0, 1]) q.1, -10*q.2))
def residualRow75 : Poly Mat3 := (basis.zip gramRow73).map (fun q => (matMul (matInv [1, 0, 0, 0, 2, -1, 0, -1, 1]) q.1, -10*q.2))
def residualRow76 : Poly Mat3 := (basis.zip gramRow74).map (fun q => (matMul (matInv [1, 0, 0, 0, 2, 1, 0, 1, 1]) q.1, -10*q.2))
def residualRow77 : Poly Mat3 := (basis.zip gramRow75).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, -1, -1, 0, 1]) q.1, -10*q.2))
def residualRow78 : Poly Mat3 := (basis.zip gramRow76).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow79 : Poly Mat3 := (basis.zip gramRow77).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, -1, -1, 1]) q.1, -10*q.2))
def residualRow80 : Poly Mat3 := (basis.zip gramRow78).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, -1, 0, 1]) q.1, -10*q.2))
def residualRow81 : Poly Mat3 := (basis.zip gramRow79).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow82 : Poly Mat3 := (basis.zip gramRow80).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow83 : Poly Mat3 := (basis.zip gramRow81).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow84 : Poly Mat3 := (basis.zip gramRow82).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 1, 0, 1]) q.1, -10*q.2))
def residualRow85 : Poly Mat3 := (basis.zip gramRow83).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 0, 1, 1, 1]) q.1, -10*q.2))
def residualRow86 : Poly Mat3 := (basis.zip gramRow84).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow87 : Poly Mat3 := (basis.zip gramRow85).map (fun q => (matMul (matInv [1, 0, 0, 1, 1, 1, 1, 0, 1]) q.1, -10*q.2))
def residualRow88 : Poly Mat3 := (basis.zip gramRow86).map (fun q => (matMul (matInv [1, 0, 0, 2, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow89 : Poly Mat3 := (basis.zip gramRow87).map (fun q => (matMul (matInv [1, 0, 1, -1, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow90 : Poly Mat3 := (basis.zip gramRow88).map (fun q => (matMul (matInv [1, 0, 1, -1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow91 : Poly Mat3 := (basis.zip gramRow89).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, -1, 0, 0, 1]) q.1, -10*q.2))
def residualRow92 : Poly Mat3 := (basis.zip gramRow90).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, -1, 0, 0]) q.1, -10*q.2))
def residualRow93 : Poly Mat3 := (basis.zip gramRow91).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, 0, -1, 1]) q.1, -10*q.2))
def residualRow94 : Poly Mat3 := (basis.zip gramRow92).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow95 : Poly Mat3 := (basis.zip gramRow93).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, 0, 1, 1]) q.1, -10*q.2))
def residualRow96 : Poly Mat3 := (basis.zip gramRow94).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 0, 1, 0, 2]) q.1, -10*q.2))
def residualRow97 : Poly Mat3 := (basis.zip gramRow95).map (fun q => (matMul (matInv [1, 0, 1, 0, 1, 1, 0, 0, 1]) q.1, -10*q.2))
def residualRow98 : Poly Mat3 := (basis.zip gramRow96).map (fun q => (matMul (matInv [1, 0, 1, 1, 1, 0, 0, 0, 1]) q.1, -10*q.2))
def residualRow99 : Poly Mat3 := (basis.zip gramRow97).map (fun q => (matMul (matInv [1, 0, 1, 1, 1, 1, 0, 0, 1]) q.1, -10*q.2))
end NuclearUltrapower.SOS
end

end OAI
end


