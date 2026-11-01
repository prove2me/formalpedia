-- Prove2me | Definitions.Def_OAIQ050L018
-- name    : OAIQ050L018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:11:25.471347+00:00
-- url     : https://prove2.me/theorems/ecfb79e8-3a2d-4b98-a3bd-53bf1062b1b1
-- title:
--   Definitions bundle OAIQ050L018 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 2 definitions and 20 theorems. The definitions and types are `OAI.Laughlin.Spin.FourCoupledIndex`, `OAI.Laughlin.Spin.wedgePairEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_FourBody_CoupledBasis`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/CoupledBasis.lean), [`Laughlin_Operators_WedgePairRotation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/WedgePairRotation.lean), [`Laughlin_Pair_CoupledBasis`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/CoupledBasis.lean), [`Laughlin_Pair_CoupledParity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/CoupledParity.lean), [`Laughlin_Polynomial_AntisymmetricCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Polynomial/AntisymmetricCoordinates.lean), [`Laughlin_Spin_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Basic.lean), [`Laughlin_Spin_LadderMatrix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/LadderMatrix.lean), [`Laughlin_Spin_TripleLadderIntertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/TripleLadderIntertwining.lean), [`Laughlin_Spin_WeightSlice`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/WeightSlice.lean).
--
--   **Imports.** It imports the bundles `OAIQ050L010`, `OAIQ050L012`, `OAIQ050L013` and `OAIQ050L014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L020` and `OAIQ050L021`; the statements `OAI_Laughlin_Fock_fourPairTargetMatrix_Fock`, `OAI_Laughlin_Spin_fourBodyTermMatrix_trace`, `OAI_Laughlin_Spin_fourBody_retained_reconstruction` and `OAI_Laughlin_Spin_threeBody_haar_compressed`; the proofs of `OAI_Laughlin_Spin_fourBodyTermMatrix_trace`, `OAI_Laughlin_Spin_normalizedCoupledDescendant_eigen`, `OAI.Laughlin.Spin.normalizedCoupledDescendant_eigen_s50`, `OAI_Laughlin_Spin_pairInclusion_raising`, `OAI.Laughlin.Spin.pairInclusion_raising_s50`, `OAI_Laughlin_Spin_threeGram_raising`, `OAI.Laughlin.Spin.threeGram_raising_s50`, `OAI_Laughlin_Spin_tripleInclusion_transpose_raising` and `OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ050L010
import Definitions.Def_OAIQ050L012
import Definitions.Def_OAIQ050L013
import Definitions.Def_OAIQ050L014

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_LadderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem raiseMatrix_row (A : ℕ) (i : Fin (A+1)) (f : Fin (A+1) → ℝ) :
    (∑ j, raiseMatrix A i j*f j) =
      if hi : i.val < A then ladder A i.val*f ⟨i.val+1,by omega⟩ else 0 := by
  by_cases hi : i.val < A
  · rw [dite_eq_left hi]
    let next : Fin (A+1) := ⟨i.val+1,by omega⟩
    have he (j : Fin (A+1)) : i.val+1=j.val ↔ next=j := by
      constructor
      · intro h; exact Fin.ext h
      · intro h; exact congrArg Fin.val h
    simp only [raiseMatrix,he,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rfl
  · rw [dite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hn : i.val+1 ≠ j.val := by omega
    simp [raiseMatrix,hn]

theorem totalRaise_apply (A B : ℕ) (f : Fin (A+1) × Fin (B+1) → ℝ)
    (i : Fin (A+1) × Fin (B+1)) :
    (∑ j, totalRaise A B i j*f j) =
      (∑ x, raiseMatrix A i.1 x*f (x,i.2)) +
      (∑ y, raiseMatrix B i.2 y*f (i.1,y)) := by
  rw [Fintype.sum_prod_type]
  simp only [totalRaise,add_mul,Finset.sum_add_distrib]
  congr 1
  · simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,
      Finset.mem_univ,ite_true]
  · rw [Finset.sum_comm]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem totalRaise_transpose_apply (A B : ℕ) (f : Fin (A+1) × Fin (B+1) → ℝ)
    (i : Fin (A+1) × Fin (B+1)) :
    (∑ j, totalRaise A B j i*f j) =
      (∑ x, f (x,i.2)*raiseMatrix A x i.1) +
      (∑ y, f (i.1,y)*raiseMatrix B y i.2) := by
  rw [Fintype.sum_prod_type]
  simp only [totalRaise,add_mul,Finset.sum_add_distrib]
  congr 1
  · simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true]
    apply Finset.sum_congr rfl
    intro x hx; ring
  · rw [Finset.sum_comm]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    apply Finset.sum_congr rfl
    intro y hy; ring

end Laughlin.Spin

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

theorem totalRaise_kronecker (A B : ℕ) :
    totalRaise A B = raiseMatrix A ⊗ₖ (1 : Matrix (Fin (B+1)) (Fin (B+1)) ℝ) +
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ raiseMatrix B := by
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_WeightSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem weightSliceIndex_injective (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    Function.Injective (weightSliceIndex A B z hA hB) := by
  intro p q h
  exact Fin.ext (congrArg (fun i => i.1.val) h)

theorem extendWeightSlice_at (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) (p : Fin (z+1)) :
    extendWeightSlice A B z hA hB f (weightSliceIndex A B z hA hB p) = f p := by
  simp only [extendWeightSlice,(weightSliceIndex_injective A B z hA hB).eq_iff,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem extendWeightSlice_off (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) (i : SpinIndex A B) (hi : i.1.val+i.2.val ≠ z) :
    extendWeightSlice A B z hA hB f i = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hne : weightSliceIndex A B z hA hB p ≠ i := by
    intro he
    have h₁ := congrArg (fun x => x.1.val) he
    have h₂ := congrArg (fun x => x.2.val) he
    dsimp [weightSliceIndex] at h₁ h₂
    omega
  simp [hne]

theorem sum_extendWeightSlice (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) (g : SpinIndex A B → ℝ) :
    (∑ i, g i*extendWeightSlice A B z hA hB f i) =
      ∑ p, g (weightSliceIndex A B z hA hB p)*f p := by
  simp only [extendWeightSlice,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem totalRaise_below_slice (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : SpinIndex A B → ℝ) (p : Fin z) :
    (totalRaise A B *ᵥ f) (⟨p.val,by omega⟩,⟨z-p.val-1,by omega⟩) =
      ladder A p.val * f (weightSliceIndex A B z hA hB ⟨p.val+1,by omega⟩) +
      ladder B (z-p.val-1)*f (weightSliceIndex A B z hA hB ⟨p.val,by omega⟩) := by
  change (∑ j, totalRaise A B _ j * f j) = _
  rw [totalRaise_apply,raiseMatrix_row,raiseMatrix_row]
  rw [dite_eq_left (show p.val < A by omega),dite_eq_left (show z-p.val-1 < B by omega)]
  have h₁ : z-(p.val+1)=z-p.val-1 := by omega
  have h₂ : z-p.val-1+1=z-p.val := by omega
  simp only [weightSliceIndex,h₁,h₂]

theorem extendWeightSlice_highest (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) (hf : ∀ p, raiseSlice A B z f p=0) :
    totalRaise A B *ᵥ extendWeightSlice A B z hA hB f = 0 := by
  funext i
  change (∑ j, totalRaise A B i j * extendWeightSlice A B z hA hB f j) = 0
  by_cases hi : i.1.val+i.2.val+1=z
  · let p : Fin z := ⟨i.1.val,by omega⟩
    have he : i = (⟨p.val,by omega⟩,⟨z-p.val-1,by omega⟩) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [p]; omega
    change (totalRaise A B *ᵥ extendWeightSlice A B z hA hB f) i = 0
    rw [he,totalRaise_below_slice A B z hA hB,extendWeightSlice_at,extendWeightSlice_at]
    exact hf p
  · rw [totalRaise_apply,raiseMatrix_row,raiseMatrix_row]
    have hx (h : i.1.val < A) :
        extendWeightSlice A B z hA hB f (⟨i.1.val+1,by omega⟩,i.2)=0 := by
      apply extendWeightSlice_off
      change i.1.val+1+i.2.val ≠ z
      omega
    have hy (h : i.2.val < B) :
        extendWeightSlice A B z hA hB f (i.1,⟨i.2.val+1,by omega⟩)=0 := by
      apply extendWeightSlice_off
      change i.1.val+(i.2.val+1) ≠ z
      omega
    split_ifs with h₁ h₂ h₂ <;> simp_all only [mul_zero,add_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericHighest_norm (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    vectorNormSq (genericHighest A B z hA hB) = 1 := by
  unfold vectorNormSq genericHighest
  simp only [pow_two]
  rw [sum_extendWeightSlice]
  simp_rw [extendWeightSlice_at,← pow_two]
  simpa only [← Fin.sum_univ_eq_sum_range] using highestUnit_norm A B z hA hB

theorem genericHighest_raising_zero (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    totalRaise A B *ᵥ genericHighest A B z hA hB = 0 := by
  apply extendWeightSlice_highest
  intro p
  exact highestUnit_raising A B z p.val hA hB p.isLt

theorem genericDescendant_succ (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) (n : ℕ) :
    genericDescendant A B z hA hB (n+1) =
      (totalRaise A B)ᵀ *ᵥ genericDescendant A B z hA hB n := by
  simp only [genericDescendant,pow_succ',Matrix.mulVec_mulVec]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericHighest_swap (Q r : ℕ) (hr : r ≤ Q) (i : SpinIndex Q Q) :
    genericHighest Q Q r hr hr i.swap = (-1 : ℝ)^r * genericHighest Q Q r hr hr i := by
  by_cases hi : i.1.val+i.2.val=r
  · let p : Fin (r+1) := ⟨i.1.val,by omega⟩
    let q : Fin (r+1) := ⟨r-i.1.val,by omega⟩
    have h1 : i = weightSliceIndex Q Q r hr hr p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    have h2 : i.swap = weightSliceIndex Q Q r hr hr q := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [weightSliceIndex,q] <;> omega
    change extendWeightSlice Q Q r hr hr _ i.swap = _ * extendWeightSlice Q Q r hr hr _ i
    rw [h2,h1,extendWeightSlice_at,extendWeightSlice_at]
    exact highestUnit_reverse Q r i.1.val (by omega)
  · change extendWeightSlice Q Q r hr hr _ i.swap = _ * extendWeightSlice Q Q r hr hr _ i
    rw [extendWeightSlice_off _ _ _ _ _ _ i hi,
      extendWeightSlice_off _ _ _ _ _ _ i.swap (by simpa [Nat.add_comm] using hi),mul_zero]

theorem totalLower_swap (Q : ℕ) (f : SpinIndex Q Q → ℝ) (i : SpinIndex Q Q) :
    ((totalRaise Q Q)ᵀ *ᵥ (fun j => f j.swap)) i =
      ((totalRaise Q Q)ᵀ *ᵥ f) i.swap := by
  change (∑ j, totalRaise Q Q j i * f j.swap) =
    ∑ j, totalRaise Q Q j i.swap * f j
  rw [totalRaise_transpose_apply,totalRaise_transpose_apply]
  exact add_comm _ _

theorem genericDescendant_swap (Q r n : ℕ) (hr : r ≤ Q) (i : SpinIndex Q Q) :
    genericDescendant Q Q r hr hr n i.swap =
      (-1 : ℝ)^r * genericDescendant Q Q r hr hr n i := by
  induction n generalizing i with
  | zero => simpa [genericDescendant] using genericHighest_swap Q r hr i
  | succ n ih =>
    rw [genericDescendant_succ]
    rw [← totalLower_swap]
    have he : (fun j => genericDescendant Q Q r hr hr n j.swap) =
      (-1 : ℝ)^r • genericDescendant Q Q r hr hr n := by funext j; exact ih j
    rw [he,Matrix.mulVec_smul]
    rfl

theorem genericUnitDescendant_swap (Q r n : ℕ) (hr : r ≤ Q) (i : SpinIndex Q Q) :
    genericUnitDescendant Q Q r hr hr n i.swap =
      (-1 : ℝ)^r * genericUnitDescendant Q Q r hr hr n i := by
  simp only [genericUnitDescendant,Pi.smul_apply,smul_eq_mul,genericDescendant_swap]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_AntisymmetricCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem antisymmetric_pairing (Q : ℕ) (f g : SpinIndex Q Q → ℝ)
    (hf : ∀ i j, f (j,i) = -f (i,j)) (hg : ∀ i j, g (j,i) = -g (i,j)) :
    (∑ i : WedgePairIndex Q, tensorToWedgePair Q f i * tensorToWedgePair Q g i) =
      ∑ i, f i * g i := by
  have hd (i : Fin (Q+1)) : f (i,i) = 0 := by have h := hf i i; linarith
  have he (i j : Fin (Q+1)) : f (i,j)*g (i,j) =
      (if i < j then f (i,j)*g (i,j) else 0) +
      (if j < i then f (j,i)*g (j,i) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h,not_lt_of_gt h,hf i j,hg i j]
  have hs : (∑ i, f i*g i) = 2 * ∑ i : SpinIndex Q Q, if i.1 < i.2 then f i*g i else 0 := by
    calc
      _ = ∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
          ((if i < j then f (i,j)*g (i,j) else 0) +
          (if j < i then f (j,i)*g (j,i) else 0)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro i hi
        apply Finset.sum_congr rfl; intro j hj
        exact he i j
      _ = _ := by
        simp only [Finset.sum_add_distrib,Fintype.sum_prod_type]
        rw [Finset.sum_comm (f := fun i j : Fin (Q+1) => if j < i then f (j,i)*g (j,i) else 0)]
        ring
  rw [hs]
  simp only [tensorToWedgePair]
  have hm (i : WedgePairIndex Q) :
      Real.sqrt 2*f i.val*(Real.sqrt 2*g i.val) = 2*(f i.val*g i.val) := by
    have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * (f i.val * g i.val) := by ring
      _ = _ := by rw [h]
  simp_rw [hm]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i : SpinIndex Q Q => i.1 < i.2)) (by simp) (fun i => f i*g i)).symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem oddPairDeficit_odd {Q : ℕ} (r : OddPairLabel Q) : Odd (oddPairDeficit r) :=
  ⟨r.val,rfl⟩

def wedgePairEquiv (Q : ℕ) : WedgePairIndex Q ≃ Σ j : Fin (Q+1), Fin j.val where
  toFun i := ⟨i.val.2,⟨i.val.1.val,i.property⟩⟩
  invFun s := ⟨(⟨s.2.val,by have := s.1.isLt; have := s.2.isLt; omega⟩,s.1),s.2.isLt⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv s := by cases s; rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CoupledBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev FourCoupledIndex (Q : ℕ) :=
  Σ r : OddPairLabel Q, GenericCoupledIndex (2*Q-2) (genericCoupledWeight Q Q (oddPairDeficit r))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_WedgePairRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

theorem antisymmetric_ordered_sum (Q : ℕ) (f g : SpinIndex Q Q → ℂ)
    (hf : ∀ i j, f (j,i) = -f (i,j)) :
    (∑ i, f i*g i) = ∑ i : WedgePairIndex Q, f i.val * (g i.val-g i.val.swap) := by
  have hd (i : Fin (Q+1)) : f (i,i)=0 := by have := hf i i; linear_combination this / 2
  have he (i j : Fin (Q+1)) : f (i,j)*g (i,j) =
      (if i < j then f (i,j)*g (i,j) else 0) -
      (if j < i then f (j,i)*g (i,j) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h,not_lt_of_gt h,hf i j]
  calc
    _ = ∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
        ((if i < j then f (i,j)*g (i,j) else 0) -
        (if j < i then f (j,i)*g (i,j) else 0)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      exact he i j
    _ = ∑ i : SpinIndex Q Q, if i.1 < i.2 then f i*(g i-g i.swap) else 0 := by
      simp only [Finset.sum_sub_distrib,Fintype.sum_prod_type]
      rw [Finset.sum_comm (f := fun i j : Fin (Q+1) => if j < i then f (j,i)*g (i,j) else 0)]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i hi
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j hj
      split_ifs <;> simp [mul_sub]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (p := fun i : SpinIndex Q Q => i.1 < i.2) (Finset.univ.filter (fun i : SpinIndex Q Q => i.1 < i.2))
        (by simp) (fun i => f i*(g i-g i.swap)))

end Laughlin.Spin

end OAI
end


