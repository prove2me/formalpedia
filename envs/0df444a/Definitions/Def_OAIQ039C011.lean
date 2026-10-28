-- Prove2me | Definitions.Def_OAIQ039C011
-- name    : OAIQ039C011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:12:46.714341+00:00
-- url     : https://prove2.me/theorems/c7c2fe46-f7dc-4b9e-abda-813597aabfad
-- title:
--   Definitions bundle OAIQ039C011 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 18 definitions, 1 inductive type or structure and 20 theorems. The definitions and types are `OAI.Kadison.FreeBlocks.tensorOutput`, `OAI.Kadison.FreeCorner.factorIsometry`, `OAI.Kadison.FreeWordAction.innerFamily`, `OAI.Kadison.GeneratedFreePair.algebra`, `OAI.Kadison.GeneratedFreePair.ambient`, `OAI.Kadison.GeneratedMatrixBicommutant.algebra`, `OAI.Kadison.GeneratedMatrixBicommutant.stages`, `OAI.Kadison.HilbertCompletion.centered`, `OAI.Kadison.HilbertDiagonal.onLp`, `OAI.Kadison.HilbertDiagonal.onSum`, `OAI.Kadison.HilbertModuleExtension.extend`, `OAI.Kadison.HilbertSequence.Pre`, `OAI.Kadison.HilbertTensor.insertLeft`, `OAI.Kadison.HilbertTensor.insertRight`, `OAI.Kadison.HilbertTensor.map`, `OAI.Kadison.HilbertTensor.pair`, `OAI.Kadison.NormalGNS.bicommutant`, `OAI.Kadison.TracialGNS.stageRepresentation`, `OAI.Kadison.completionIsometry`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CompletionCentered`, `Commutator_EndpointGNS2`, `Commutator_FreeInnerFamily`, `Commutator_FreeRepeatedWords`, `Commutator_GeneratedFreePair`, `Commutator_GeneratedMatrixBicommutant`, `Commutator_HilbertDiagonal`, `Commutator_HilbertModuleExtension`, `Commutator_HilbertSequence`, `Commutator_IsometryCompression`, `Commutator_MatrixTowerGNS`, `Commutator_TensorActions`, `Commutator_TensorDevelopment`, `Commutator_TensorMultiplicity`, `Commutator_TensorMultiplicity2`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C026` and `OAIQ039C027`; the statements `OAI.Kadison.Decomposable.exists_common_tests`, `OAI.Kadison.GeneratedMatrixBicommutant.factor`, `OAI.Kadison.GeneratedMatrixBicommutant.in_range`, `OAI.Kadison.GeneratedMatrixBicommutant.le_vonNeumann`, `OAI.Kadison.MatrixModule.endpoint_unit_bound`, `OAI.Kadison.SeparableTest.seminorm_bound` and `OAI.Kadison.exists_separable_cstar_bicommutant`; the proofs of `OAI.Kadison.Decomposable.uniform_commutator_in_central_spectral_model_nonzero`, `OAI.Kadison.HilbertPadding.norm_extend_commutator` and `OAI.Kadison.MatrixModule.endpoint_unit_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_CompletionCentered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.HilbertCompletion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

abbrev centered (Ω : E) : Submodule ℂ E := (ℂ ∙ Ω)ᗮ

end Kadison.HilbertCompletion
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison

open UniformSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def completionIsometry (U : E →ₗᵢ[ℂ] F) : Completion E →ₗᵢ[ℂ] Completion F where
  toLinearMap := U.toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

@[simp] lemma completionIsometry_coe (U : E →ₗᵢ[ℂ] F) (x : E) :
    completionIsometry U (x : Completion E) = (U x : Completion F) := by
  change U.toContinuousLinearMap.completion (x : Completion E) = _
  simp

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorDevelopment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter

namespace Kadison

namespace HilbertTensor

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable {G H : Type*}
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

noncomputable def map (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] H) :=
  (TensorProduct.mapL f g).completion

@[simp] lemma map_coe_tmul (f : E →L[𝕜] F) (g : G →L[𝕜] H) (x : E) (y : G) :
    map f g ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] G) : Completion (E ⊗[𝕜] G)) =
      ((f x ⊗ₜ[𝕜] g y : F ⊗[𝕜] H) : Completion (F ⊗[𝕜] H)) := by
  simp [map]

end HilbertTensor

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointGNS2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion

namespace Kadison.TracialGNS

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

noncomputable def stageRepresentation (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) :
    Matrix I I ℂ →⋆ₐ[ℂ] (τ.GNS →L[ℂ] τ.GNS) := τ.gnsStarAlgHom.comp φ

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeInnerFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct CStarAlgebra

open UniformSpace

namespace Kadison.FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (f : D →⋆ₐ[ℂ] A) {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι)
  (hS : S i=f.range)

def innerFamily (u : unitary D) (k : ι) : A ≃⋆ₐ[ℂ] A := by
  classical
  exact if k=i then Unitary.conjStarAlgAut ℂ A (⟨f (u:D),Unitary.map_mem f u.property⟩)
    else StarAlgEquiv.refl ℂ A

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
@[simp] lemma innerFamily_self (u : unitary D) (a : A) :
    innerFamily f i u i a=f (u:D)*a*f (star (u:D)) := by
  simp [innerFamily,map_star]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma innerFamily_other (u : unitary D) {k : ι} (hk : k≠i) (a : A) :
    innerFamily f i u k a=a := by simp [innerFamily,hk]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
include hS in
lemma innerFamily_mem (u : unitary D) (k : ι) (a : A) (ha : a∈S k) :
    innerFamily f i u k a∈S k := by
  by_cases hk : k=i
  · subst k
    rw [innerFamily_self]
    have hf (d : D) : f d∈S i := by rw [hS]; exact ⟨d,rfl⟩
    exact mul_mem (mul_mem (hf _) ha) (hf _)
  · simpa only [innerFamily_other f i u hk a] using ha

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma innerFamily_one (k : ι) (a : A) : innerFamily f i 1 k a=a := by
  by_cases hk : k=i
  · subst k; simp
  · exact innerFamily_other f i 1 hk a

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma innerFamily_mul (u v : unitary D) (k : ι) (a : A) :
    innerFamily f i (u*v) k a=innerFamily f i u k (innerFamily f i v k a) := by
  by_cases hk : k=i
  · subst k
    rw [innerFamily_self,innerFamily_self,innerFamily_self]
    change f ((u:D)*(v:D))*a*f (star ((u:D)*(v:D))) =
      f (u:D)*(f (v:D)*a*f (star (v:D)))*f (star (u:D))
    rw [map_mul,star_mul,map_mul]
    simp only [mul_assoc]
  · simp only [innerFamily_other f i _ hk]

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.HilbertTensor

variable {E F J K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def pair (x : E) (a : J) : Completion (E ⊗[ℂ] J) := (x ⊗ₜ[ℂ] a : E ⊗[ℂ] J)

@[simp] lemma inner_pair (x y : E) (a b : J) :
    inner ℂ (pair x a) (pair y b) = inner ℂ x y * inner ℂ a b := by
  simp only [pair, Completion.inner_coe, TensorProduct.inner_tmul]

@[simp] lemma norm_pair (x : E) (a : J) : ‖pair x a‖ = ‖x‖ * ‖a‖ := by
  simp only [pair, Completion.norm_coe, TensorProduct.norm_tmul]

def insertRight (a : J) : E →L[ℂ] Completion (E ⊗[ℂ] J) :=
  Completion.toComplL.comp ((TensorProduct.mkL ℂ E J).flip a)

@[simp] lemma insertRight_apply (a : J) (x : E) : insertRight a x = pair x a := rfl

def insertLeft (x : E) : J →L[ℂ] Completion (E ⊗[ℂ] J) :=
  Completion.toComplL.comp (TensorProduct.mkL ℂ E J x)

@[simp] lemma insertLeft_apply (x : E) (a : J) : insertLeft x a = pair x a := rfl

@[simp] lemma insertRight_adjoint_pair [CompleteSpace E] (b : J) (x : E) (a : J) :
    (insertRight b).adjoint (pair x a) = inner ℂ b a • x := by
  apply (ext_inner_left ℂ)
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, insertRight_apply, inner_pair, inner_smul_right]
  exact mul_comm _ _

@[simp] lemma insertLeft_adjoint_pair [CompleteSpace J] (y : E) (x : E) (a : J) :
    (insertLeft y).adjoint (pair x a) = inner ℂ y x • a := by
  apply (ext_inner_left ℂ)
  intro b
  rw [ContinuousLinearMap.adjoint_inner_right, insertLeft_apply, inner_pair, inner_smul_right]

end Kadison.HilbertTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorMultiplicity2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.HilbertTensor

variable {E F J K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

@[simp] lemma map_pair (f : E →L[ℂ] F) (g : J →L[ℂ] K) (x : E) (a : J) :
    map f g (pair x a) = pair (f x) (g a) := map_coe_tmul _ _ _ _

end Kadison.HilbertTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeRepeatedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeBlocks

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {ι : Type*}
  (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hij : i≠j)

def tensorOutput {Left Right Target : Type*}
    [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
    [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]
    [NormedAddCommGroup Target] [InnerProductSpace ℂ Target]
    (embedding : Completion (Left ⊗[ℂ] Right) →ₗᵢ[ℂ] Target) (vector : Left) :
    Right →L[ℂ] Target :=
  embedding.toContinuousLinearMap.comp (HilbertTensor.insertLeft vector)

lemma norm_tensorOutput {Left Right Target : Type*}
    [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
    [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]
    [NormedAddCommGroup Target] [InnerProductSpace ℂ Target]
    (embedding : Completion (Left ⊗[ℂ] Right) →ₗᵢ[ℂ] Target)
    (vector : Left) (value : Right) :
    ‖tensorOutput embedding vector value‖ = ‖vector‖ * ‖value‖ := by
  change ‖embedding (HilbertTensor.pair vector value)‖ = _
  rw [embedding.norm_map, HilbertTensor.norm_pair]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure Pre (ω : Ultrafilter ℕ) (H : Type*) [NormedAddCommGroup H] where
  seq : ℕ →ᵇ H

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.NormalGNS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def bicommutant (S : StarSubalgebra ℂ (K →L[ℂ] K)) : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (S : Set (K →L[ℂ] K)))
  centralizer_centralizer' := by
    have h : ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (S : Set (K →L[ℂ] K)))) :
        StarSubalgebra ℂ (K →L[ℂ] K)).carrier =
        Set.centralizer (Set.centralizer (S : Set (K →L[ℂ] K))) := by
      exact (StarSubalgebra.coe_centralizer_centralizer ℂ _).trans (by
        rw [StarMemClass.star_coe_eq,Set.union_self])
    change _ = ((StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (S : Set (K →L[ℂ] K)))) : StarSubalgebra ℂ (K →L[ℂ] K)).carrier
    rw [h]
    simp only [Set.centralizer_centralizer_centralizer]

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal

namespace Kadison.HilbertDiagonal

variable {ι : Type*} (E : ι → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

def onLp (V : ∀ i, E i →ₗᵢ[ℂ] E i) : lp E 2 →ₗᵢ[ℂ] lp E 2 where
  toFun x := ⟨fun i => V i (x i), (lp.memℓp x).mono' (fun i => le_of_eq ((V i).norm_map _))⟩
  map_add' _ _ := by ext i; exact (V i).map_add _ _
  map_smul' _ _ := by ext i; exact (V i).map_smul _ _
  norm_map' x := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    congr 2
    funext i
    exact congrArg (fun a : ℝ => a ^ (2 : ℝ≥0∞).toReal) ((V i).norm_map (x i))

@[simp] lemma onLp_apply (V : ∀ i, E i →ₗᵢ[ℂ] E i) (x : lp E 2) (i : ι) :
    onLp E V x i=V i (x i) := rfl

@[simp] lemma onLp_single [DecidableEq ι] (V : ∀ i, E i →ₗᵢ[ℂ] E i) (i : ι) (x : E i) :
    onLp E V (lp.single 2 i x)=lp.single 2 i (V i x) := by
  ext j
  by_cases hji : j=i
  · subst j
    simp only [onLp_apply,lp.single_apply,Pi.single_eq_same]
  · simp only [onLp_apply,lp.single_apply,Pi.single_eq_of_ne hji,map_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : ∀ i, E i →ₗᵢ[ℂ] H) (hU : IsHilbertSum ℂ E U)

def onSum (V : ∀ i, E i →ₗᵢ[ℂ] E i) : H →ₗᵢ[ℂ] H :=
  hU.linearIsometryEquiv.symm.toLinearIsometry.comp
    ((onLp E V).comp hU.linearIsometryEquiv.toLinearIsometry)

@[simp] lemma onSum_insert (V : ∀ i, E i →ₗᵢ[ℂ] E i) (i : ι) (x : E i) :
    onSum E U hU V (U i x)=U i (V i x) := by
  classical
  have he : hU.linearIsometryEquiv (U i x)=lp.single 2 i x := by
    rw [←hU.linearIsometryEquiv_symm_apply_single x,LinearIsometryEquiv.apply_symm_apply]
  change hU.linearIsometryEquiv.symm (onLp E V (hU.linearIsometryEquiv (U i x))) = _
  rw [he,onLp_single,hU.linearIsometryEquiv_symm_apply_single]

end Kadison.HilbertDiagonal
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertModuleExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ENNReal

open ContinuousLinearMap

namespace Kadison.HilbertModuleExtension

variable {ι E F K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (V : ι → E →ₗᵢ[ℂ] K) (W : ι → F →ₗᵢ[ℂ] H)
  (hV : IsHilbertSum ℂ (fun _ : ι => E) V) (hW : IsHilbertSum ℂ (fun _ : ι => F) W)

def extend (T : E →L[ℂ] F) : K →L[ℂ] H :=
  hW.linearIsometryEquiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)).comp
      hV.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap)

end Kadison.HilbertModuleExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedFreePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.GeneratedFreePair

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (D : VonNeumannAlgebra H) (k : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def algebra : VonNeumannAlgebra H := NormalGNS.bicommutant (D.toStarSubalgebra⊔k.range)

def ambient (b : Bool) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  if b then k.range else D.toStarSubalgebra

end Kadison.GeneratedFreePair

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedMatrixBicommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.GeneratedMatrixBicommutant

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] A)

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def stages : StarSubalgebra ℂ (H →L[ℂ] H) := ⨆ n,(φ.comp (stage n)).range

def algebra : VonNeumannAlgebra H := NormalGNS.bicommutant (stages size stage φ)

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_IsometryCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open ContinuousLinearMap

namespace Kadison.FreeCorner

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

lemma isometry_adjoint_apply (F : K →ₗᵢ[ℂ] H) (x : K) :
    F.toContinuousLinearMap.adjoint (F x)=x :=
  congrArg (fun T : K →L[ℂ] K => T x) F.adjoint_comp_self

omit [CompleteSpace L] in
lemma isometry_project_range (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) (x : L) :
    F (F.toContinuousLinearMap.adjoint (E x))=E x := by
  obtain ⟨y,hy⟩ := hEF (Set.mem_range_self x)
  rw [←hy,isometry_adjoint_apply]

def factorIsometry (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) : L →ₗᵢ[ℂ] K where
  toLinearMap := (F.toContinuousLinearMap.adjoint.comp E.toContinuousLinearMap).toLinearMap
  norm_map' x := by
    change ‖F.toContinuousLinearMap.adjoint (E x)‖=‖x‖
    rw [←F.norm_map,isometry_project_range E F hEF,E.norm_map]

end Kadison.FreeCorner

end

end
end

end OAI
end


