-- Prove2me | Definitions.Def_BooleanFun_Basic
-- name    : BooleanFun_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T19:02:38.044182+00:00
-- url     : https://prove2.me/theorems/e8e33e53-4e51-4aad-9caa-497607c403fb
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Joris Roos and contributors's pinned Boolean functions and Arrow’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Basic.lean

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
set_option autoImplicit false
namespace BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
abbrev BooleanFunc (n : ℕ) : Type := (Fin n → Fin 2) → ℝ
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
def expectation : BooleanFunc n →ₗ[ℝ] ℝ := {
  toFun := fun f ↦ (1 / 2) ^ n * ∑ i, f i
  map_add' := by
    intro f g
    simp only [one_div, inv_pow, Pi.add_apply]
    rw [sum_add_distrib]
    ring
  map_smul' := by
    intro c f
    dsimp
    rw [← mul_sum]
    ring
}
scoped notation "𝐄" => expectation
abbrev walshCharacter (S : Finset (Fin n)) : BooleanFunc n := fun x ↦ ∏ i ∈ S, (-1) ^ (x i).val
scoped notation "χ" => walshCharacter
abbrev BooleanFunc' n := Finset (Fin n) → ℝ
def fourierTransform : BooleanFunc n →ₗ[ℝ] BooleanFunc' n := {
  toFun := fun f ↦ fun S ↦ 𝐄 (χ S * f)
  map_add' := by
    intro f g
    funext S
    simp
    ring_nf
    simp
  map_smul' := by
    intro c f
    funext S
    simp
}
scoped notation "𝓕" => fourierTransform
theorem expectation_prod_self_nonneg : 0 ≤ 𝐄 (f * f) := by
  apply mul_nonneg
  · norm_num
  · apply sum_nonneg
    intros x _
    apply mul_self_nonneg
instance : InnerProductSpace.Core ℝ (BooleanFunc n) := {
  inner := fun f g ↦ 𝐄 (f * g)
  conj_inner_symm := by
    intros f g
    simp only [conj_trivial]
    rw [mul_comm]
  re_inner_nonneg := by
    intro f
    simp only [RCLike.re_to_real, expectation_prod_self_nonneg]
  add_left := by simp only [add_mul, map_add, implies_true]
  smul_left := by
    simp only [Algebra.smul_mul_assoc, map_smul, smul_eq_mul, conj_trivial, implies_true]
  definite := by
    intro h; simp [expectation]
    rw [Finset.sum_eq_zero_iff_of_nonneg]
    . simp; intro i; ext j; simp [i]
    . intro i _; apply mul_self_nonneg

}
instance : NormedAddCommGroup (BooleanFunc n) :=
  instCoreRealBooleanFunc.toNormedAddCommGroup
instance : SeminormedAddCommGroup (BooleanFunc n) :=
  instNormedAddCommGroupBooleanFunc.toSeminormedAddCommGroup
instance : InnerProductSpace ℝ (BooleanFunc n) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (BooleanFunc n))
instance : Norm (BooleanFunc n) := InnerProductSpace.Core.toNorm (𝕜 := ℝ) (F := BooleanFunc n)
@[simp]
lemma walsh_sq_eq_one : (χ S) ^ 2 = 1 := by
  funext x
  unfold walshCharacter
  simp only [Pi.pow_apply, Pi.one_apply]
  rw [← prod_pow]
  ring_nf
  simp
@[simp]
lemma expectation_one : @expectation n 1 = 1 := by simp [expectation]
lemma norm_sq_eq_inner : ‖f‖ ^ 2 = ⟪f, f⟫ := by
  simpa only [RCLike.re_to_real] using
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) f)
@[simp]
theorem walsh_norm_one (S : Finset (Fin n)) : ‖χ S‖ = 1 := by
  simp only [norm_eq_sqrt_real_inner, sqrt_eq_one]
  change 𝐄 _ = 1
  rw [← pow_two, walsh_sq_eq_one]
  simp
@[simp]
theorem walsh_inner_self_eq_one : ⟪χ S, χ S⟫ = 1 := by
  rw [← norm_sq_eq_inner, walsh_norm_one, one_pow]
theorem walsh_mul_eq : χ S * χ S' = χ (symmDiff S S') := by
  funext x
  unfold walshCharacter
  simp
  nth_rewrite 1 [← sdiff_union_inter S S']
  nth_rewrite 3 [← sdiff_union_inter S' S]
  repeat rw [prod_union (disjoint_sdiff_inter _ _)]
  rw [inter_comm S]
  ring_nf
  have haux : (∏ i ∈ S' ∩ S, ((-1 : ℝ) ^ (x i).val)) ^ 2 = 1 := by
    rw [← prod_pow]; ring_nf; simp
  rw [haux, mul_one, ← prod_union]
  · rfl
  · simp only [disjoint_iff_ne, mem_sdiff, ne_eq, and_imp]
    intro _ ha _ _ _ _ h
    rw [h] at ha
    contradiction
def flipAt (i₀ : Fin n) (x : Fin n → Fin 2) : Fin n → Fin 2 := fun i ↦ if i = i₀ then 1 - x i else x i
@[simp]
lemma flipAt_flipped {i₀ : Fin n} {x : Fin n → Fin 2} : flipAt i₀ x i₀ = 1 - x i₀ := by
  unfold flipAt
  split_ifs <;> tauto
@[simp]
lemma flipAt_flipAt_eq {i₀ : Fin n} {x : Fin n → Fin 2} : flipAt i₀ (flipAt i₀ x) = x := by
  unfold flipAt
  funext i
  split_ifs
  · rw [sub_sub_cancel]
  · rfl
@[simp]
theorem expectation_walsh_eq_zero (hS : S.Nonempty) : 𝐄 (χ S) = 0 := by
  simp [expectation, walshCharacter]
  obtain ⟨i₀, hi₀⟩ := hS
  let e : (Fin n → Fin 2) ≃ (Fin n → Fin 2) := Equiv.addRight (Pi.single i₀ 1)

  have h_add_one (b : Fin 2) : (-1 : ℝ) ^ (b + 1).val = - ((-1) ^ b.val) := by fin_cases b <;> simp

  have : ∀ x, χ S (e x) = - χ S x := by
    intro x; unfold walshCharacter e
    simp [Pi.single_apply, ← Finset.prod_erase_mul S _ hi₀, h_add_one (x i₀), mul_neg]
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (Finset.ne_of_mem_erase hi), add_zero]
  have h_sum := e.sum_comp (χ S)
  simp [this] at h_sum
  linarith [this]
theorem walsh_orthogonal {S S' : Finset (Fin n)} (h : S ≠ S') : ⟪χ S, χ S'⟫ = 0 := by
  change 𝐄 _ = 0
  rw [walsh_mul_eq]
  apply expectation_walsh_eq_zero
  by_contra h1
  simp at h1
  exact h h1
theorem walsh_orthonormal : Orthonormal (ι := Finset (Fin n)) ℝ χ := ⟨walsh_norm_one, @walsh_orthogonal _⟩
abbrev walsh_basis : Module.Basis (ι := Finset (Fin n)) ℝ (BooleanFunc n) :=
  basisOfOrthonormalOfCardEqFinrank (v := χ) walsh_orthonormal (by simp)
abbrev walsh_orthonormal_basis : OrthonormalBasis (ι := Finset (Fin n)) ℝ (BooleanFunc n) :=
  Module.Basis.toOrthonormalBasis (basisOfOrthonormalOfCardEqFinrank (v := χ) walsh_orthonormal (by simp))
    (by simp [walsh_orthonormal])
@[simp]
lemma walsh_orthonormal_basis_apply (T : Finset (Fin n)) : walsh_orthonormal_basis T = χ T := by
  simp [walsh_orthonormal_basis]
abbrev setAt (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i ↦ if i = i₀ then v else x i
@[simp]
lemma setAt_it (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) : setAt i₀ v x i₀ = v := by
  unfold setAt; split_ifs <;> tauto
def dderiv (i : Fin n) : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun := fun f ↦ fun x ↦ (f (setAt i 0 x) - f (setAt i 1 x)) / 2
  map_add' := by intros; funext; simp only [Pi.add_apply]; ring
  map_smul' := by intros; funext; dsimp; ring
def laplace (i : Fin n) : BooleanFunc n →ₗ[ℝ] BooleanFunc n := {
  toFun := fun f ↦ fun x ↦ (f x - f (flipAt i x)) / 2
  map_add' := by intros; funext; simp only [Pi.add_apply]; ring
  map_smul' := by intros; funext; dsimp; ring
}
abbrev influence (f : BooleanFunc n) (i : Fin n) : ℝ := 𝐄 ((laplace i f) ^ 2)
abbrev totalInfluence (f : BooleanFunc n) : ℝ := ∑ i, influence f i
abbrev covariance (f g : BooleanFunc n) : ℝ := 𝐄 (f * g) - 𝐄 f * 𝐄 g
abbrev variance (f : BooleanFunc n) : ℝ := covariance f f
section FourierWeight
abbrev fourierWeight (k : ℕ) (f : BooleanFunc n) : ℝ := ∑ S ∈ {S | S.card = k}, |𝓕 f S| ^ 2
abbrev fourierWeightOne (f : BooleanFunc n) : ℝ := ∑ i, |𝓕 f {i}| ^ 2
end FourierWeight
section Multiplier
def multiplier (m : ℕ → ℝ) : BooleanFunc n →ₗ[ℝ] BooleanFunc n := {
  toFun := fun f ↦ ∑ S : Finset (Fin n), (m S.card) • 𝓕 f S • χ S
  map_add' := by
    intros; ext; dsimp
    repeat rw [Finset.sum_apply]
    rw [← sum_add_distrib, sum_congr (by rfl)]
    intros
    simp only [map_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' := by
    intros; ext
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, RingHom.id_apply, mul_sum]
    congr! 1; ring
}
abbrev noise_operator (ρ : ℝ) : BooleanFunc n →ₗ[ℝ] BooleanFunc n := multiplier (ρ^·)
abbrev noise_stability (ρ : ℝ) (f : BooleanFunc n) := ⟪f, noise_operator ρ f⟫
end Multiplier
section Convolution
abbrev convolution (f g : BooleanFunc n) : BooleanFunc n := fun x ↦ 𝐄 (fun y ↦ (f y) * (g (x + y)))
infixl : 67 "⋆" => convolution
end Convolution
end
end BooleanFun


