-- Prove2me | solution 1 for Arxiv1705_08274.doubling_exiting_intensities
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T05:20:23.706456+00:00
-- url     : https://prove2.me/submissions/795579c3-1bd1-4937-9fc8-193b73f005e5

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace S79DE
open Arxiv1705_08274
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma step (Q : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hc : CanAdd Q Q) :
    IsSymmetricResponse (addResp Q Q) := by
  set A := Q.toBlocks₁₁
  set B := Q.toBlocks₁₂
  have hdet : IsUnit (1 - B * B).det := by
    have := hc
    rw [CanAdd, wMinus, Matrix.det_fromBlocks_one₁₁] at this
    simpa using this
  set M := (1 - B * B)⁻¹
  have hM : (1 - B * B) * M = 1 := Matrix.mul_nonsing_inv _ hdet
  have hW : (wMinus B B)⁻¹ = fromBlocks M (B * M) (B * M) M := by
    apply Matrix.inv_eq_right_inv
    rw [wMinus, fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · convert hM using 1; rw [Matrix.sub_mul, Matrix.mul_assoc]; simp [sub_eq_add_neg]
    · simp
    · simp
    · convert hM using 1; rw [Matrix.sub_mul, Matrix.mul_assoc]; simp [sub_eq_add_neg, add_comm]
  have : addResp Q Q = wPlus A A * ((wMinus B B)⁻¹ * wPlus A A) + fromBlocks 0 B B 0 := rfl
  rw [this, hW, wPlus, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add, IsSymmetricResponse]
  simp

lemma dbl_symm (R : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hR : IsSymmetricResponse R) (k : ℕ)
    (h : ∀ j, j < k → CanAdd (dblSeq R j) (dblSeq R j)) : IsSymmetricResponse (dblSeq R k) := by
  cases k with
  | zero => exact hR
  | succ k => exact step _ (h k (Nat.lt_succ_self k))

end S79DE

open Arxiv1705_08274 S79DE in
theorem solution {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (Tn Rf : Matrix (Dir N) (Dir N) ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hdbl : ∀ j, j < k → CanAdd (dblSeq (fromBlocks Tn Rf Rf Tn) j) (dblSeq (fromBlocks Tn Rf Rf Tn) j))
    (lam0 : ℝ) (hlam0 : 0 ≤ lam0) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (I0m I0p Inm Inp : Dir N → ℝ)
    (h30 : Sum.elim I0m Inp = dblSeq (fromBlocks Tn Rf Rf Tn) k *ᵥ Sum.elim Inm I0p)
    (h32 : Inm = ((2 * lam0) • (reflArray D * S.muMat * S.wMat)) *ᵥ Inp)
    (hK : IsUnit (1 - (2 * lam0) • ((dblSeq (fromBlocks Tn Rf Rf Tn) k).toBlocks₁₂ *
      reflArray D * S.muMat * S.wMat)).det) :
    let Q₁₁ := (dblSeq (fromBlocks Tn Rf Rf Tn) k).toBlocks₁₁
    let Q₁₂ := (dblSeq (fromBlocks Tn Rf Rf Tn) k).toBlocks₁₂
    let K := 1 - (2 * lam0) • (Q₁₂ * reflArray D * S.muMat * S.wMat)
    IsSymmetricResponse (dblSeq (fromBlocks Tn Rf Rf Tn) k) ∧
    Inp = (K⁻¹ * Q₁₁) *ᵥ I0p ∧
    Inm = ((2 * lam0) • (reflArray D * S.muMat * S.wMat) * K⁻¹ * Q₁₁) *ᵥ I0p ∧
    I0m = (Q₁₂ + (2 * lam0) • (Q₁₁ * reflArray D * S.muMat * S.wMat * K⁻¹ * Q₁₁)) *ᵥ I0p := by
  intro Q₁₁ Q₁₂ K
  have hsym : IsSymmetricResponse (dblSeq (fromBlocks Tn Rf Rf Tn) k) :=
    dbl_symm _ (by simp [IsSymmetricResponse]) k hdbl
  set Q := dblSeq (fromBlocks Tn Rf Rf Tn) k with hQ
  set G := (2 * lam0) • (reflArray D * S.muMat * S.wMat)
  have hQe : Q = fromBlocks Q₁₁ Q₁₂ Q₁₂ Q₁₁ := by
    conv_lhs => rw [← fromBlocks_toBlocks Q]
    rw [← hsym.1, ← hsym.2]
  rw [hQe, fromBlocks_mulVec] at h30
  have e1 : I0m = Q₁₁ *ᵥ Inm + Q₁₂ *ᵥ I0p := by
    funext i; have := congrFun h30 (Sum.inl i); simpa using this
  have e2 : Inp = Q₁₂ *ᵥ Inm + Q₁₁ *ᵥ I0p := by
    funext i; have := congrFun h30 (Sum.inr i); simpa using this
  have hKe : K = 1 - Q₁₂ * G := by
    simp only [K, G, Matrix.mul_smul, Matrix.mul_assoc]
  have hKv : K *ᵥ Inp = Q₁₁ *ᵥ I0p := by
    rw [hKe, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← h32]
    rw [e2]; abel
  have hKu : IsUnit K.det := hK
  have h2 : Inp = (K⁻¹ * Q₁₁) *ᵥ I0p := by
    rw [← Matrix.mulVec_mulVec, ← hKv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hKu,
      Matrix.one_mulVec]
  have h3 : Inm = (G * K⁻¹ * Q₁₁) *ᵥ I0p := by
    rw [h32, h2, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨hsym, h2, h3, ?_⟩
  rw [e1, h3, Matrix.add_mulVec, add_comm]
  congr 1
  simp only [G, Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
