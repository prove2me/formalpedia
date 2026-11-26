-- Prove2me | solution 1 for Arxiv2205_09423.translated_slab_matrices
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T01:53:15.190287+00:00
-- url     : https://prove2.me/submissions/37df0f2e-2632-490c-bc1f-dfa01ee70dae

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open Arxiv2205_09423

namespace S75TS

variable {Nk N : ℕ}

lemma phase_shift (K : ModeSet Nk) (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (L0 : ℝ)
    (vin vout : Fin (2 * Nk + 1) → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    blockSum K A (shiftZ L0 r) vin vout j i =
      Complex.exp (Complex.I * (((vin i 2 - vout j 2) * L0 : ℝ) : ℂ)) •
        blockSum K A r vin vout j i := by
  unfold blockSum
  conv_rhs => rw [smul_smul, mul_comm, ← smul_smul, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  simp only [shiftZ, dotProduct_add]
  have : dotProduct (vin i - vout j) ![0, 0, L0] = (vin i 2 - vout j 2) * L0 := by
    simp [dotProduct, Fin.sum_univ_three]
  rw [this]; push_cast; ring

lemma asm_conj (B B' : Fin (2 * Nk + 1) → Fin (2 * Nk + 1) → Matrix (Fin 2) (Fin 2) ℂ)
    (f g : Fin (2 * Nk + 1) → ℂ) (h : ∀ j i, B' j i = (g j * f i) • B j i) :
    assemble B' = diagonal (fun x : MIdx Nk => g x.1) * assemble B *
      diagonal (fun x : MIdx Nk => f x.1) := by
  ext x y
  simp only [assemble, Matrix.of_apply, diagonal_mul, mul_diagonal, h, Matrix.smul_apply,
    smul_eq_mul]
  ring

lemma kron_diag (d : Fin (2 * Nk + 1) → ℂ) :
    Matrix.kroneckerMap (· * ·) (diagonal d) (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      diagonal (fun x : MIdx Nk => d x.1) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [kroneckerMap_apply, diagonal_apply, one_apply, Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = e <;> simp [h1, h2]

noncomputable def P (K : ModeSet Nk) (L0 : ℝ) (i : Fin (2 * Nk + 1)) : ℂ :=
  Complex.exp (Complex.I * ((K.kz i * L0 : ℝ) : ℂ))
noncomputable def M (K : ModeSet Nk) (L0 : ℝ) (i : Fin (2 * Nk + 1)) : ℂ :=
  Complex.exp (-(Complex.I * ((K.kz i * L0 : ℝ) : ℂ)))

lemma lamPlus_eq (K : ModeSet Nk) (L0 : ℝ) :
    lamPlus K L0 = diagonal (fun x : MIdx Nk => P K L0 x.1) := by
  unfold lamPlus; rw [kron_diag]; rfl

lemma star_P (K : ModeSet Nk) (L0 : ℝ) (i : Fin (2 * Nk + 1)) : star (P K L0 i) = M K L0 i := by
  unfold P M
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

lemma star_M (K : ModeSet Nk) (L0 : ℝ) (i : Fin (2 * Nk + 1)) : star (M K L0 i) = P K L0 i := by
  rw [← star_P, star_star]

lemma lamMinus_eq (K : ModeSet Nk) (L0 : ℝ) :
    lamMinus K L0 = diagonal (fun x : MIdx Nk => M K L0 x.1) := by
  unfold lamMinus; rw [lamPlus_eq]
  ext x y
  simp only [Matrix.map_apply, diagonal_apply]
  split_ifs <;> simp [star_P]

lemma PM (K : ModeSet Nk) (L0 : ℝ) (i : Fin (2 * Nk + 1)) : P K L0 i * M K L0 i = 1 := by
  unfold P M; rw [← Complex.exp_add]; simp

lemma DE (K : ModeSet Nk) (L0 : ℝ) :
    diagonal (fun x : MIdx Nk => P K L0 x.1) * diagonal (fun x : MIdx Nk => M K L0 x.1) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext x; exact PM _ _ _

lemma ED (K : ModeSet Nk) (L0 : ℝ) :
    diagonal (fun x : MIdx Nk => M K L0 x.1) * diagonal (fun x : MIdx Nk => P K L0 x.1) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext x; rw [mul_comm]; exact PM _ _ _

lemma kz2 (K : ModeSet Nk) (i : Fin (2 * Nk + 1)) : K.kvec i 2 = K.kz i := by
  simp [ModeSet.kvec]
lemma kzT2 (K : ModeSet Nk) (i : Fin (2 * Nk + 1)) : K.kvecT i 2 = -K.kz i := by
  simp [ModeSet.kvecT]

lemma split_phase (a b L0 : ℝ) : Complex.exp (Complex.I * (((a - b) * L0 : ℝ) : ℂ)) =
    Complex.exp (-(Complex.I * ((b * L0 : ℝ) : ℂ))) * Complex.exp (Complex.I * ((a * L0 : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

end S75TS

open S75TS in
theorem solution {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL : ℝ)
    (hdL : 0 < dL) (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ)
    (hr : ∀ p, r p 2 ∈ Set.Icc (-dL / 2) (dL / 2)) (L0 : ℝ) :
    (∀ j i, tbar K A (shiftZ L0 r) j i =
      Complex.exp (Complex.I * (((K.kz i - K.kz j) * L0 : ℝ) : ℂ)) • tbar K A r j i) ∧
    assemble (tbar K A (shiftZ L0 r)) = lamMinus K L0 * assemble (tbar K A r) * lamPlus K L0 ∧
    sMat K A (shiftZ L0 r) = lamPM K L0 * sMat K A r * lamPM K L0 ∧
    (IsUnit (assemble (tpbar K A r)).det →
      transfer (sMat K A (shiftZ L0 r)) = lamMP K L0 * transfer (sMat K A r) * lamPM K L0) := by
  have ht : ∀ j i, tbar K A (shiftZ L0 r) j i =
      Complex.exp (Complex.I * (((K.kz i - K.kz j) * L0 : ℝ) : ℂ)) • tbar K A r j i := by
    intro j i
    unfold tbar
    rw [phase_shift, kz2, kz2, smul_add]
    congr 1
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hT : assemble (tbar K A (shiftZ L0 r)) =
      diagonal (fun x : MIdx Nk => M K L0 x.1) * assemble (tbar K A r) *
        diagonal (fun x : MIdx Nk => P K L0 x.1) := by
    apply asm_conj; intro j i; rw [ht, split_phase]; rfl
  have hR : assemble (rbar K A (shiftZ L0 r)) =
      diagonal (fun x : MIdx Nk => P K L0 x.1) * assemble (rbar K A r) *
        diagonal (fun x : MIdx Nk => P K L0 x.1) := by
    apply asm_conj; intro j i
    unfold rbar; rw [phase_shift, kz2, kzT2, sub_neg_eq_add]
    congr 1; unfold P; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hTp : assemble (tpbar K A (shiftZ L0 r)) =
      diagonal (fun x : MIdx Nk => P K L0 x.1) * assemble (tpbar K A r) *
        diagonal (fun x : MIdx Nk => M K L0 x.1) := by
    apply asm_conj; intro j i
    unfold tpbar; rw [phase_shift, kzT2, kzT2, smul_add]
    by_cases hij : i = j
    · subst hij; rw [PM, one_smul]; simp
    · simp only [hij, if_false, smul_zero, zero_add]
      congr 1; unfold P M; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hRp : assemble (rpbar K A (shiftZ L0 r)) =
      diagonal (fun x : MIdx Nk => M K L0 x.1) * assemble (rpbar K A r) *
        diagonal (fun x : MIdx Nk => M K L0 x.1) := by
    apply asm_conj; intro j i
    unfold rpbar; rw [phase_shift, kz2, kzT2]
    congr 1; unfold M; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hS : sMat K A (shiftZ L0 r) = lamPM K L0 * sMat K A r * lamPM K L0 := by
    unfold sMat lamPM
    rw [hT, hR, hTp, hRp, lamPlus_eq, lamMinus_eq, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_assoc]
  refine ⟨ht, by rw [hT, lamPlus_eq, lamMinus_eq], hS, fun _ => ?_⟩
  set D := diagonal (fun x : MIdx Nk => P K L0 x.1)
  set E := diagonal (fun x : MIdx Nk => M K L0 x.1)
  have hDE : D * E = 1 := DE K L0
  have hED : E * D = 1 := ED K L0
  have hMP : lamMP K L0 = Matrix.fromBlocks E 0 0 D := by
    unfold lamMP lamPM
    rw [lamPlus_eq, lamMinus_eq, Matrix.fromBlocks_map]
    congr 1
    · ext x y; simp only [Matrix.map_apply, diagonal_apply, E]; split_ifs <;> simp [star_P]
    · simp
    · simp
    · ext x y; simp only [Matrix.map_apply, diagonal_apply, D]; split_ifs <;> simp [star_M]
  have hinv : ∀ X : Matrix (MIdx Nk) (MIdx Nk) ℂ, (D * X * E)⁻¹ = D * X⁻¹ * E := by
    intro X
    have hD : D⁻¹ = E := Matrix.inv_eq_right_inv hDE
    have hE : E⁻¹ = D := Matrix.inv_eq_right_inv hED
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hD, hE, Matrix.mul_assoc]
  rw [hS, hMP]
  unfold sMat lamPM transfer
  rw [lamPlus_eq, lamMinus_eq]
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  rw [hinv]
  congr 1
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc E D, hED, Matrix.one_mul, ← Matrix.mul_assoc E D, hED, Matrix.one_mul]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc E D, hED, Matrix.one_mul]
  · simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    rw [← Matrix.mul_assoc E D, hED, Matrix.one_mul]
