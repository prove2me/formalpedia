-- Prove2me | Definitions.Def_OAIQ050L011
-- name    : OAIQ050L011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:09:14.331986+00:00
-- url     : https://prove2.me/theorems/5437b1cf-1d9b-4c3d-8f68-a28e9ddd92e5
-- title:
--   Definitions bundle OAIQ050L011 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 11 definitions and 17 theorems. The definitions and types are `OAI.Laughlin.Fock.complexThreeGram`, `OAI.Laughlin.Rotation.sourceSpinMatrix`, `OAI.Laughlin.Rotation.sourceTensorRepresentation`, `OAI.Laughlin.Rotation.tensorWeightRepresentative`, `OAI.Laughlin.Spin.PairOrbitalIndex`, `OAI.Laughlin.Spin.TripleIndex`, `OAI.Laughlin.Spin.swap23`, `OAI.Laughlin.Spin.swap23Matrix`, `OAI.Laughlin.Spin.swapCompression`, `OAI.Laughlin.Spin.threeGram`, `OAI.Laughlin.Spin.tripleInclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_Polynomial_SymmetricTensorCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Polynomial/SymmetricTensorCoordinates.lean), [`Laughlin_Polynomial_SymmetricTensorOrbit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Polynomial/SymmetricTensorOrbit.lean), [`Laughlin_Polynomial_SymmetricTensorRange`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Polynomial/SymmetricTensorRange.lean), [`Laughlin_Spin_Representation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Representation.lean), [`Laughlin_Spin_TensorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/TensorAction.lean), [`Laughlin_Spin_TripleLadderIntertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/TripleLadderIntertwining.lean), [`Laughlin_ThreeBody_PhysicalKernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/PhysicalKernel.lean), [`Laughlin_ThreeBody_SpinCovariance`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/SpinCovariance.lean).
--
--   **Imports.** It imports the bundles `OAIQ050L003`, `OAIQ050L004`, `OAIQ050L006` and `OAIQ050L007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L016`, `OAIQ050L017` and `OAIQ050L019`; the statements `OAI_Laughlin_Fock_limitFourEnd_four_create`, `OAI_Laughlin_Fock_physical_threeBody_budget_eventually`, `OAI_Laughlin_Fock_sourcePairCreate_inner`, `OAI.Laughlin.Fock.sourcePairCreate_inner_s50`, `OAI_Laughlin_Fock_sourcePair_normal_order`, `OAI_Laughlin_Fock_sourceThreeEnd_rotation`, `OAI_Laughlin_Fock_threeWedge_contraction_zero`, `OAI_Laughlin_Fock_threeWedge_inner`, `OAI_Laughlin_Spin_threeGram_on_slice`, `OAI_Laughlin_Spin_threeGram_raising` and `OAI.Laughlin.Spin.threeGram_raising_s50`; the proofs of `OAI_Laughlin_Fock_limitFourEnd_four_create`, `OAI_Laughlin_Fock_sourcePairCreate_inner`, `OAI.Laughlin.Fock.sourcePairCreate_inner_s50`, `OAI_Laughlin_Fock_sourcePair_normal_order`, `OAI_Laughlin_Fock_sourceThreeEnd_rotation`, `OAI_Laughlin_Fock_threeWedge_contraction_zero`, `OAI_Laughlin_Fock_threeWedge_inner` and `OAI_Laughlin_Spin_threeGram_on_slice`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L007

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TensorAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem tensorMatrix_one (N : ℕ) : tensorMatrix N 1 = 1 := by
  classical
  ext a b
  simp only [tensorMatrix,Matrix.one_apply]
  by_cases h : a=b
  · subst b; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

noncomputable def sourceTensorRepresentation (Q : ℕ) : SourceSU2 →*
    Matrix (Fin Q → Fin 2) (Fin Q → Fin 2) ℂ where
  toFun g := tensorMatrix Q g.val
  map_one' := tensorMatrix_one Q
  map_mul' g h := tensorMatrix_mul Q g.val h.val

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_SymmetricTensorCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem tensorWeight_count (Q p : ℕ) :
    (∑ a : Fin Q → Fin 2, if tensorWeight Q a=p then (1 : ℝ) else 0) = Q.choose p := by
  classical
  have he : (∑ a : Fin Q → Fin 2, if tensorWeight Q a=p then (1 : ℝ) else 0) =
      ∑ s : Finset (Fin Q), if s.card=p then (1 : ℝ) else 0 :=
    (tensorSubsetEquiv Q).sum_comp (fun s => if s.card=p then (1 : ℝ) else 0)
  rw [he]
  have hs : (Finset.univ.filter (fun s : Finset (Fin Q) => s.card=p)) =
      (Finset.univ : Finset (Fin Q)).powersetCard p := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [← Finset.sum_filter]
  rw [hs]
  simp

theorem symmetricTensorInclusionReal_isometry (Q : ℕ) :
    (symmetricTensorInclusionReal Q)ᵀ*symmetricTensorInclusionReal Q=1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,symmetricTensorInclusionReal]
  by_cases hpq : p=q
  · subst q
    rw [ite_eq_left rfl]
    have hn : (Q.choose p.val : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.choose_pos (by omega : p.val ≤ Q)))
    have he (a : Fin Q → Fin 2) :
        (if tensorWeight Q a=p.val then (Real.sqrt (Q.choose p.val : ℝ))⁻¹ else 0) *
        (if tensorWeight Q a=p.val then (Real.sqrt (Q.choose p.val : ℝ))⁻¹ else 0) =
        ((Real.sqrt (Q.choose p.val : ℝ))⁻¹)^2 * (if tensorWeight Q a=p.val then 1 else 0) := by
      split_ifs <;> ring
    simp_rw [he,← Finset.mul_sum,tensorWeight_count]
    rw [inv_pow,Real.sq_sqrt (by positivity),inv_mul_cancel₀ hn]
  · rw [ite_eq_right hpq]
    apply Finset.sum_eq_zero
    intro a ha
    have h : p.val ≠ q.val := fun h => hpq (Fin.ext h)
    split_ifs <;> simp_all

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_SymmetricTensorOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem tensorWeight_perm (Q : ℕ) (a : Fin Q → Fin 2) (σ : Equiv.Perm (Fin Q)) :
    tensorWeight Q (a ∘ σ)=tensorWeight Q a := by
  have he : tensorBits Q (a ∘ σ) = (tensorBits Q a).map σ.symm.toEmbedding := by
    ext i
    simp [tensorBits]
  unfold tensorWeight
  rw [he,Finset.card_map]

theorem tensorWeight_eq_exists_perm (Q : ℕ) (a b : Fin Q → Fin 2)
    (h : tensorWeight Q a=tensorWeight Q b) :
    ∃ σ : Equiv.Perm (Fin Q), a ∘ σ=b := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_map_finset_eq (tensorBits Q a) (tensorBits Q b) h
  refine ⟨σ.symm,?_⟩
  funext i
  have hm := congrArg (fun s : Finset (Fin Q) => i ∈ s) hσ
  have hh : a (σ.symm i)=1 ↔ b i=1 := by simpa [tensorBits] using Iff.of_eq hm
  apply Fin.ext
  simp only [Fin.ext_iff,Fin.val_one] at hh
  have ha := (a (σ.symm i)).isLt
  have hb := (b i).isLt
  dsimp [Function.comp_def]
  omega

 theorem tensorMatrix_perm (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin Q → Fin 2) (σ : Equiv.Perm (Fin Q)) :
    tensorMatrix Q A (a ∘ σ) (b ∘ σ)=tensorMatrix Q A a b := by
  exact Equiv.prod_comp σ (fun i => A (a i) (b i))

theorem tensorMatrix_preserves_symmetric (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (Fin Q → Fin 2) → ℂ)
    (hv : ∀ a b, tensorWeight Q a=tensorWeight Q b → v a=v b) :
    ∀ a b, tensorWeight Q a=tensorWeight Q b →
      (tensorMatrix Q A *ᵥ v) a=(tensorMatrix Q A *ᵥ v) b := by
  intro a b hab
  obtain ⟨σ,rfl⟩ := tensorWeight_eq_exists_perm Q a b hab
  have he := (tensorPermutation Q σ).sum_comp (fun c => tensorMatrix Q A (a ∘ σ) c*v c)
  change (∑ c, tensorMatrix Q A a c*v c) = ∑ c, tensorMatrix Q A (a ∘ σ) c*v c
  rw [← he]
  apply Finset.sum_congr rfl
  intro c hc
  change tensorMatrix Q A a c*v c = tensorMatrix Q A (a ∘ σ) (c ∘ σ)*v (c ∘ σ)
  rw [tensorMatrix_perm,hv (c ∘ σ) c (tensorWeight_perm Q c σ)]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_SymmetricTensorRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem tensorWeight_le (Q : ℕ) (a : Fin Q → Fin 2) : tensorWeight Q a ≤ Q := by
  have h := Finset.card_le_card (Finset.filter_subset (fun i => a i=1) (Finset.univ : Finset (Fin Q)))
  simpa [tensorWeight,tensorBits] using h

 theorem tensorWeight_surjective (Q : ℕ) (p : Fin (Q+1)) : ∃ a : Fin Q → Fin 2, tensorWeight Q a=p.val := by
  by_contra h
  push Not at h
  have hc := tensorWeight_count Q p.val
  simp only [ite_eq_right (h _),Finset.sum_const_zero] at hc
  have hp : (0 : ℝ) < Q.choose p.val := by exact_mod_cast Nat.choose_pos (by omega : p.val ≤ Q)
  linarith

noncomputable def tensorWeightRepresentative (Q : ℕ) (p : Fin (Q+1)) : Fin Q → Fin 2 :=
  Classical.choose (tensorWeight_surjective Q p)
 theorem tensorWeightRepresentative_weight (Q : ℕ) (p : Fin (Q+1)) :
    tensorWeight Q (tensorWeightRepresentative Q p)=p.val := Classical.choose_spec (tensorWeight_surjective Q p)

theorem symmetricTensorInclusion_isometry (Q : ℕ) :
    (symmetricTensorInclusion Q)ᴴ * symmetricTensorInclusion Q=1 := by
  ext p q
  have h := congrArg Complex.ofReal (congrFun (congrFun (symmetricTensorInclusionReal_isometry Q) p) q)
  simpa [symmetricTensorInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
    Matrix.one_apply,apply_ite] using h

 theorem symmetricTensorInclusion_mulVec (Q : ℕ) (w : Fin (Q+1) → ℂ) (a : Fin Q → Fin 2) :
    (symmetricTensorInclusion Q *ᵥ w) a =
      ((Real.sqrt (Q.choose (tensorWeight Q a) : ℝ))⁻¹ : ℂ) *
        w ⟨tensorWeight Q a,by have := tensorWeight_le Q a; omega⟩ := by
  classical
  let p : Fin (Q+1) := ⟨tensorWeight Q a,by have := tensorWeight_le Q a; omega⟩
  change (∑ q, (symmetricTensorInclusion Q) a q * w q) = _
  rw [Finset.sum_eq_single p]
  · simp [symmetricTensorInclusion,symmetricTensorInclusionReal,p]
  · intro q hq hqp
    have hn : tensorWeight Q a ≠ q.val := by intro h; exact hqp (Fin.ext h.symm)
    simp [symmetricTensorInclusion,symmetricTensorInclusionReal,hn]
  · simp

theorem symmetricTensor_range (Q : ℕ) (v : (Fin Q → Fin 2) → ℂ)
    (hv : ∀ a b, tensorWeight Q a=tensorWeight Q b → v a=v b) :
    ∃ w : Fin (Q+1) → ℂ, symmetricTensorInclusion Q *ᵥ w=v := by
  let w : Fin (Q+1) → ℂ := fun p => (Real.sqrt (Q.choose p.val : ℝ) : ℂ) *
    v (tensorWeightRepresentative Q p)
  refine ⟨w,?_⟩
  funext a
  rw [symmetricTensorInclusion_mulVec]
  dsimp [w]
  have hn : (Real.sqrt (Q.choose (tensorWeight Q a) : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast Nat.choose_pos (tensorWeight_le Q a)
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
  apply hv
  exact tensorWeightRepresentative_weight Q _

 theorem symmetricTensor_projector_fixed (Q : ℕ) (v : (Fin Q → Fin 2) → ℂ)
    (hv : ∀ a b, tensorWeight Q a=tensorWeight Q b → v a=v b) :
    (symmetricTensorInclusion Q*(symmetricTensorInclusion Q)ᴴ) *ᵥ v=v := by
  obtain ⟨w,rfl⟩ := symmetricTensor_range Q v hv
  rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,symmetricTensorInclusion_isometry,Matrix.mul_one]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def sourceSpinMatrix (Q : ℕ) (g : SourceSU2) : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ :=
  (symmetricTensorInclusion Q)ᴴ * sourceTensorRepresentation Q g * symmetricTensorInclusion Q

 theorem tensor_spin_intertwining (Q : ℕ) (g : SourceSU2) :
    symmetricTensorInclusion Q*sourceSpinMatrix Q g = sourceTensorRepresentation Q g*symmetricTensorInclusion Q := by
  ext a p
  let v : (Fin Q → Fin 2) → ℂ := fun b => symmetricTensorInclusion Q b p
  have hv : ∀ b c, tensorWeight Q b=tensorWeight Q c → v b=v c := by
    intro b c h
    simp only [v,symmetricTensorInclusion,Matrix.map_apply,symmetricTensorInclusionReal,h]
  have hf := tensorMatrix_preserves_symmetric Q g.val v hv
  have he := congrFun (symmetricTensor_projector_fixed Q (sourceTensorRepresentation Q g *ᵥ v) hf) a
  change (symmetricTensorInclusion Q*((symmetricTensorInclusion Q)ᴴ*sourceTensorRepresentation Q g*symmetricTensorInclusion Q)) a p = _
  calc
    _ = ((symmetricTensorInclusion Q*(symmetricTensorInclusion Q)ᴴ)*
      (sourceTensorRepresentation Q g*symmetricTensorInclusion Q)) a p := by simp only [Matrix.mul_assoc]
    _ = _ := he

 theorem sourceSpinMatrix_mul (Q : ℕ) (g h : SourceSU2) :
    sourceSpinMatrix Q (g*h)=sourceSpinMatrix Q g*sourceSpinMatrix Q h := by
  unfold sourceSpinMatrix
  rw [map_mul]
  have he := tensor_spin_intertwining Q h
  unfold sourceSpinMatrix at he
  calc
    _ = (symmetricTensorInclusion Q)ᴴ*sourceTensorRepresentation Q g*
        (sourceTensorRepresentation Q h*symmetricTensorInclusion Q) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← he]; simp only [Matrix.mul_assoc]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TripleLadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

abbrev TripleIndex (Q : ℕ) := (Orbital Q × Orbital Q) × Orbital Q
abbrev PairOrbitalIndex (Q : ℕ) := Fin ((2*Q-2)+1) × Orbital Q

noncomputable def tripleInclusion (Q : ℕ) : Matrix (TripleIndex Q) (PairOrbitalIndex Q) ℝ :=
  pairInclusion Q ⊗ₖ (1 : Matrix (Orbital Q) (Orbital Q) ℝ)

def swap23 {Q : ℕ} (i : TripleIndex Q) : TripleIndex Q := ((i.1.1,i.2),i.1.2)

@[simp] theorem swap23_involutive {Q : ℕ} (i : TripleIndex Q) : swap23 (swap23 i) = i := by
  rcases i with ⟨⟨i,j⟩,k⟩; rfl

noncomputable def swap23Matrix (Q : ℕ) : Matrix (TripleIndex Q) (TripleIndex Q) ℝ :=
  fun i j => if swap23 i=j then 1 else 0

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SpinCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def swapCompression (Q : ℕ) : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  (tripleInclusion Q)ᵀ * swap23Matrix Q * tripleInclusion Q

noncomputable def threeGram (Q : ℕ) : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  1 - (2 : ℝ) • swapCompression Q

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

noncomputable def complexThreeGram (Q : ℕ) :
    Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℂ :=
  fun a b => (Spin.threeGram Q a b : ℂ)

end Laughlin.Fock

end OAI
end


