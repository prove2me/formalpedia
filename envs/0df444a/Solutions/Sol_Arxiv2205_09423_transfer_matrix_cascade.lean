-- Prove2me | solution 1 for Arxiv2205_09423.transfer_matrix_cascade
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T01:55:15.00628+00:00
-- url     : https://prove2.me/submissions/7fd8f6ee-d6c7-4908-8afd-de993dc29063

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
theorem ts_main {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL : ℝ)
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

namespace S75TC
open S75TS
variable {Nk : ℕ}

lemma PM' (K : ModeSet Nk) (a b : ℝ) (i : Fin (2 * Nk + 1)) :
    P K a i * M K b i = P K (a - b) i := by
  unfold P M; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma MP' (K : ModeSet Nk) (a b : ℝ) (i : Fin (2 * Nk + 1)) :
    M K a i * P K b i = M K (a - b) i := by
  unfold P M; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma lamPM_diag (K : ModeSet Nk) (a : ℝ) : lamPM K a =
    diagonal (Sum.elim (fun x : MIdx Nk => P K a x.1) (fun x : MIdx Nk => M K a x.1)) := by
  unfold lamPM; rw [lamPlus_eq, lamMinus_eq, fromBlocks_diagonal]

lemma lamMP_diag (K : ModeSet Nk) (a : ℝ) : lamMP K a =
    diagonal (Sum.elim (fun x : MIdx Nk => M K a x.1) (fun x : MIdx Nk => P K a x.1)) := by
  unfold lamMP; rw [lamPM_diag, diagonal_map (star_zero _)]
  congr 1; funext x; cases x <;> simp [star_P, star_M]

lemma Lp_Lm (K : ModeSet Nk) (a b : ℝ) : lamPM K a * lamMP K b = lamPM K (a - b) := by
  rw [lamPM_diag, lamMP_diag, lamPM_diag, diagonal_mul_diagonal]
  congr 1; funext x; cases x <;> simp [PM', MP']

lemma Lm_Lp (K : ModeSet Nk) (a b : ℝ) : lamMP K a * lamPM K b = lamMP K (a - b) := by
  rw [lamPM_diag, lamMP_diag, lamMP_diag, diagonal_mul_diagonal]
  congr 1; funext x; cases x <;> simp [PM', MP']

lemma Lp0 (K : ModeSet Nk) : lamPM K 0 = 1 := by
  rw [lamPM_diag, ← diagonal_one]; congr 1; funext x; cases x <;> simp [P, M]

lemma prod_succ {α : Type*} [Monoid α] (f : ℕ → α) (n : ℕ) :
    ((List.range (n + 1)).map f).reverse.prod = f n * ((List.range n).map f).reverse.prod := by
  rw [List.range_succ, List.map_append, List.reverse_append]; simp

end S75TC

open S75TS S75TC in
theorem solution {Nk : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (M : ℕ) (hM : 0 < M)
    (Np : ℕ → ℕ) (A : ∀ l, Fin (Np l) → Amp) (r : ∀ l, Fin (Np l) → Fin 3 → ℝ)
    (dL : ℕ → ℝ) (hdL : ∀ l, 0 < dL l) (hr : ∀ l p, r l p 2 ∈ Set.Icc (-dL l / 2) (dL l / 2))
    (hinv : ∀ l, IsUnit (assemble (tpbar K (A l) (r l))).det)
    (L : ℕ → ℝ) (hL : ∀ l, l + 1 < M → L l < L (l + 1)) :
    let M0 := fun l => transfer (sMat K (A l) (r l))
    let ML := fun l => transfer (sMat K (A l) (shiftZ (L l) (r l)))
    ((List.range M).map ML).reverse.prod =
        lamMP K (L (M - 1)) *
          ((List.range M).map fun l =>
            M0 l * lamPM K (L l - if l = 0 then 0 else L (l - 1))).reverse.prod ∧
    (∀ D : ℝ, (∀ l, dL l = D) → L 0 = 0 → (∀ l, l + 1 < M → L (l + 1) - L l = D) →
      ((List.range M).map ML).reverse.prod =
        lamMP K (M * D) * ((List.range M).map fun l => lamPM K D * M0 l).reverse.prod) ∧
    ∀ L' : ℝ, ∃ ph : Fin (2 * Nk + 1) ⊕ Fin (2 * Nk + 1) → ℂ, (∀ s, ‖ph s‖ = 1) ∧
      ∀ (X : Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ) x y,
        (lamMP K L' * X) x y = ph (Sum.map Prod.fst Prod.fst x) * X x y := by
  intro M0 ML
  have hML : ∀ l, ML l = lamMP K (L l) * M0 l * lamPM K (L l) := fun l =>
    (ts_main K hK (dL l) (hdL l) (A l) (r l) (hr l) (L l)).2.2.2 (hinv l)
  set g : ℕ → Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ :=
    fun l => M0 l * lamPM K (L l - if l = 0 then 0 else L (l - 1)) with hg
  have part1 : ∀ n, 1 ≤ n → ((List.range n).map ML).reverse.prod =
      lamMP K (L (n - 1)) * ((List.range n).map g).reverse.prod := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [hML, hg, Matrix.mul_assoc]
      · rw [prod_succ, prod_succ, ih hn0, hML]
        simp only [Nat.add_sub_cancel, hg, if_neg (Nat.pos_iff_ne_zero.1 hn0)]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (lamPM K (L n)), Lp_Lm]
  refine ⟨part1 M hM, ?_, ?_⟩
  · intro D _ hL0 hD
    rw [part1 M hM]
    have hH : ∀ n, 1 ≤ n → n ≤ M →
        ((List.range n).map fun l => lamPM K D * M0 l).reverse.prod =
          lamPM K D * ((List.range n).map g).reverse.prod := by
      intro n hn hnM
      induction n with
      | zero => omega
      | succ n ih =>
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp [hg, hL0, Lp0]
        · rw [prod_succ, prod_succ, ih hn0 (by omega)]
          simp only [hg, if_neg (Nat.pos_iff_ne_zero.1 hn0)]
          have := hD (n - 1) (by omega)
          rw [show n - 1 + 1 = n by omega] at this
          rw [this]
          simp only [Matrix.mul_assoc]
    have hLl : ∀ l, l < M → L l = l * D := by
      intro l hl
      induction l with
      | zero => simp [hL0]
      | succ l ih =>
        have := hD l hl
        rw [ih (by omega)] at this
        push_cast; linarith
    rw [hH M hM le_rfl, ← Matrix.mul_assoc, Lm_Lp, hLl (M - 1) (by omega)]
    congr 2
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  · intro L'
    refine ⟨Sum.elim (S75TS.M K L') (S75TS.P K L'), ?_, ?_⟩
    · intro s; cases s <;> simp [S75TS.P, S75TS.M, Complex.norm_exp]
    · intro X x y
      rw [lamMP_diag, diagonal_mul]
      cases x <;> rfl
