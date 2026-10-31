-- Prove2me | solution 1 for AlgebraicPCSP.OneInThree.theorem_8_1_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:59:14.574999+00:00
-- url     : https://prove2.me/submissions/54a67478-7ce0-4d54-87e7-a56548bc402a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices
import Theorems.Thm_AlgebraicPCSP_OneInThree_lemma_8_10
import Theorems.Thm_AlgebraicPCSP_OneInThree_proposition_8_12
import Theorems.Thm_AlgebraicPCSP_OneInThree_section_8_4_pigeonhole

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.OneInThree

namespace Thm81CoreProof

lemma seg_zero_eq_zeroMat (p : ℕ) : seg p 0 = zeroMat p := by
  ext r c
  simp [seg, toMatrix, segTuple, zeroMat]

lemma seg_sq_eq_oneMat (p : ℕ) : seg p (p * p) = oneMat p := by
  funext r c
  simp only [seg, toMatrix, segTuple, oneMat, (finProdFinEquiv (r, c)).isLt, if_true]

lemma card_filter_val_lt {N k : ℕ} (hk : k ≤ N) :
    (Finset.univ.filter (fun idx : Fin N => idx.val < k)).card = k := by
  have himg : Finset.image Fin.val (Finset.univ.filter (fun idx : Fin N => idx.val < k)) =
      Finset.range k := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨idx, hlt, rfl⟩
      exact hlt
    · intro hlt
      exact ⟨⟨m, lt_of_lt_of_le hlt hk⟩, hlt, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

lemma sum_colMatrix_col {p : ℕ} (h : Fin p → ℕ) (hh : ∀ j, h j ≤ p) (j : Fin p) :
    (∑ i : Fin p, ((colMatrix p h i j).val : ℚ)) = (h j : ℚ) := by
  have hval : ∀ i : Fin p, ((colMatrix p h i j).val : ℚ) = if i.val < h j then 1 else 0 := by
    intro i
    unfold colMatrix
    split_ifs <;> rfl
  simp_rw [hval]
  simp [Finset.sum_boole, card_filter_val_lt (hh j)]

lemma area_almost_rect {p k l m : ℕ} (hlk : l ≤ k) (hkp : k ≤ p) (hmp : m ≤ p) :
    area (colMatrix p (fun j => if j.val < m then k else l)) =
      ((m * k + (p - m) * l : ℕ) : ℚ) / (p : ℚ) ^ 2 := by
  unfold area
  congr 1
  rw [Finset.sum_comm]
  have hh : ∀ j : Fin p, (if j.val < m then k else l) ≤ p := by
    intro j
    split_ifs <;> omega
  simp_rw [sum_colMatrix_col _ hh]
  have hsub : (k : ℚ) = (l : ℚ) + ((k - l : ℕ) : ℚ) := by
    exact_mod_cast (Nat.add_sub_of_le hlk).symm
  have hite : ∀ j : Fin p, ((if j.val < m then k else l : ℕ) : ℚ) =
      (l : ℚ) + if j.val < m then ((k - l : ℕ) : ℚ) else 0 := by
    intro j
    split_ifs <;> linarith
  simp_rw [hite, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    card_filter_val_lt hmp, nsmul_eq_mul]
  push_cast
  have hmp_q : (m : ℚ) ≤ (p : ℚ) := by exact_mod_cast hmp
  have hlk_q : (l : ℚ) ≤ (k : ℚ) := by exact_mod_cast hlk
  rw [Nat.cast_sub hmp, Nat.cast_sub hlk]
  ring

lemma prime_sq_eq_three_mul_add_one {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ∃ q : ℕ, p * p = 3 * q + 1 := by
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
    have hne0 : p % 3 ≠ 0 := by
      intro h0
      have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega
    omega
  refine ⟨(p * p) / 3, ?_⟩
  have hsq : (p * p) % 3 = 1 := by
    rw [Nat.mul_mod]
    rcases hmod with h | h <;> rw [h]
  omega

end Thm81CoreProof

theorem solution {D : Type} [Fintype D] [DecidableEq D] (R : Set (Fin 3 → D))
    (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    (p : ℕ) (hp : p.Prime) (hpD : 60 * Fintype.card D < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) :
    False := by
  have hD_pos : 0 < Fintype.card D := Fintype.card_pos_iff.mpr ⟨f 0⟩
  have hp3 : 3 < p := by omega
  obtain ⟨q, hq⟩ := Thm81CoreProof.prime_sq_eq_three_mul_add_one hp hp3
  obtain ⟨l₁, l₂, hl₁_low, hl₁₂, hl₂_high, hs_eq⟩ := section_8_4_pigeonhole f hp hpD s
  have hl₁_bound : p < 3 * l₁ + 6 * Fintype.card D := by
    have hq1 : (p : ℚ) < 3 * (l₁ : ℚ) + 6 * (Fintype.card D : ℚ) := by linarith
    exact_mod_cast hq1
  have hl₂_bound : 3 * l₂ < p := by
    have hq2 : 3 * (l₂ : ℚ) < (p : ℚ) := by linarith
    exact_mod_cast hq2
  let b := 5 * Fintype.card D
  let k := l₁ + b
  have hb_pos : 0 < b := by dsimp [b]; omega
  have hpl₁_le_q : p * l₁ ≤ q := by nlinarith
  let m := (q - p * l₁) / b
  have hmd_le : m * b ≤ q - p * l₁ := Nat.div_mul_le_self (q - p * l₁) b
  have hlt_succ : q - p * l₁ < b * (m + 1) := Nat.lt_mul_div_succ (q - p * l₁) hb_pos
  have h2_raw : 3 * q < 3 * (p * l₁) + 6 * Fintype.card D * p := by nlinarith
  have h2 : 3 * (q - p * l₁) < 6 * Fintype.card D * p := by omega
  have h3 : 3 * (m * (5 * Fintype.card D)) < 6 * Fintype.card D * p := by
    calc 3 * (m * (5 * Fintype.card D)) = 3 * (m * b) := rfl
    _ ≤ 3 * (q - p * l₁) := by omega
    _ < 6 * Fintype.card D * p := h2
  have hm_lt : 5 * m < 2 * p := by nlinarith
  have hm_bound : m ≤ p := by omega
  have hpm_gt : b < p - m := by dsimp [b]; omega
  have hl₁_le_k : l₁ ≤ k := by dsimp [k]; omega
  have hl₂_le_k : l₂ ≤ k := by dsimp [k, b]; omega
  have hk_le_p : k ≤ p := by dsimp [k, b]; omega
  let X₁ := colMatrix p (fun j => if j.val < m then k else l₁)
  let X₂ := colMatrix p (fun j => if j.val < m then k else l₂)
  have hX₁_rect : IsAlmostRectangle (5 * Fintype.card D) X₁ :=
    ⟨k, l₁, m, hl₁_le_k, hk_le_p, hm_bound, by dsimp [k, b]; omega, rfl⟩
  have hX₂_rect : IsAlmostRectangle (5 * Fintype.card D) X₂ :=
    ⟨k, l₂, m, hl₂_le_k, hk_le_p, hm_bound, by dsimp [k, b]; omega, rfl⟩
  have hX₁_tame : IsTame f g s X₁ := proposition_8_12 R f g hf hg hp hpD s hs hcyc X₁ hX₁_rect
  have hX₂_tame : IsTame f g s X₂ := proposition_8_12 R f g hf hg hp hpD s hs hcyc X₂ hX₂_rect
  have hX₁_eq_X₂ : GEquiv f g s X₁ X₂ := by
    unfold GEquiv tOp
    congr 2
    ext j
    by_cases hj : j.val < m
    · simp [X₁, X₂, colMatrix, hj]
    · simp only [X₁, X₂, colMatrix, hj, ↓reduceIte]
      exact hs_eq
  have hp2_val : (p : ℚ) ^ 2 = 3 * (q : ℚ) + 1 := by
    have hq_rat : ((p * p : ℕ) : ℚ) = ((3 * q + 1 : ℕ) : ℚ) := by rw [hq]
    push_cast at hq_rat
    linarith
  have hp2_pos : (0 : ℚ) < (p : ℚ) ^ 2 := by linarith
  have hones₁ : m * k + (p - m) * l₁ ≤ q := by
    have : m * (l₁ + b) + (p - m) * l₁ = p * l₁ + m * b := by
      zify [hm_bound]
      ring
    dsimp [k]
    omega
  have harea₁ : area X₁ < 1 / 3 := by
    rw [Thm81CoreProof.area_almost_rect hl₁_le_k hk_le_p hm_bound, div_lt_iff₀ hp2_pos]
    have h_rat : ((m * k + (p - m) * l₁ : ℕ) : ℚ) ≤ (q : ℚ) := by exact_mod_cast hones₁
    linarith
  have hones₂ : q + 1 ≤ m * k + (p - m) * l₂ := by
    have h1 : p * l₁ + m * b + (p - m) ≤ m * (l₁ + b) + (p - m) * l₂ := by
      have hdiff : 1 ≤ l₂ - l₁ := by omega
      have hmul : p - m ≤ (p - m) * (l₂ - l₁) := by nlinarith
      zify [hm_bound, hl₁₂.le] at hmul ⊢
      linarith
    have h2' : q + 1 ≤ p * l₁ + b * (m + 1) := by omega
    have h3 : b * (m + 1) = m * b + b := by ring
    dsimp [k]
    omega
  have harea₂ : 1 / 3 < area X₂ := by
    rw [Thm81CoreProof.area_almost_rect hl₂_le_k hk_le_p hm_bound, lt_div_iff₀ hp2_pos]
    have h_rat : (q : ℚ) + 1 ≤ ((m * k + (p - m) * l₂ : ℕ) : ℚ) := by exact_mod_cast hones₂
    linarith
  have hX₁_zero : GEquiv f g s X₁ (zeroMat p) := by
    rcases hX₁_tame with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · exfalso; linarith
  have hX₂_one : GEquiv f g s X₂ (oneMat p) := by
    rcases hX₂_tame with ⟨_, h⟩ | ⟨h, _⟩
    · exfalso; linarith
    · exact h
  have h0_one : GEquiv f g s (seg p 0) (seg p (p * p)) := by
    rw [Thm81CoreProof.seg_zero_eq_zeroMat, Thm81CoreProof.seg_sq_eq_oneMat]
    exact hX₁_zero.symm.trans (hX₁_eq_X₂.trans hX₂_one)
  exact (lemma_8_10 R f g hf hg hp hp3 s hs hcyc).2 h0_one
