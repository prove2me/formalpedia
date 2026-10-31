-- Prove2me | solution 1 for AlgebraicPCSP.OneInThree.lemma_8_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:47:46.971746+00:00
-- url     : https://prove2.me/submissions/bb662885-ca8a-4ac8-9d63-eb1b55690b5f

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices
import Theorems.Thm_AlgebraicPCSP_OneInThree_lemma_8_7
import Theorems.Thm_AlgebraicPCSP_OneInThree_lemma_8_8

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.OneInThree

namespace Lemma810Proof

lemma isCyclic_iterate {D : Type} {n : ℕ} (t : (Fin n → D) → D) (hcyc : IsCyclic t)
    (a : Fin n → D) (m : ℕ) :
    t a = t (a ∘ (finRotate n)^[m]) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    rw [hcyc a, ih (a ∘ finRotate n), Function.iterate_succ', Function.comp_assoc]

lemma val_finRotate {N : ℕ} (i : Fin N) :
    (finRotate N i).val = (i.val + 1) % N := by
  rcases N with _ | n
  · exact i.elim0
  · rcases i with ⟨k, hk⟩
    by_cases h : k < n
    · rw [finRotate_of_lt h]
      exact (Nat.mod_eq_of_lt (Nat.succ_lt_succ h)).symm
    · have hk_eq : k = n := by omega
      subst hk_eq
      rw [finRotate_last']
      simp

lemma val_finRotate_iterate {N : ℕ} (m : ℕ) (i : Fin N) :
    ((finRotate N)^[m] i).val = (i.val + m) % N := by
  induction m generalizing i with
  | zero =>
    simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, val_finRotate, Nat.mod_add_mod, Nat.add_right_comm,
      Nat.add_assoc]

lemma mod_eq_ite {a N : ℕ} (h : a < 2 * N) :
    a % N = if a < N then a else a - N := by
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

lemma val_segTuple {p k : ℕ} (idx : Fin (p * p)) :
    (segTuple p k idx).val = if idx.val < k then 1 else 0 := by
  unfold segTuple
  split_ifs <;> rfl

lemma tOp_toMatrix_comp {D : Type} {p : ℕ} (f : Fin 2 → D) (s : (Fin p → D) → D)
    (x : Fin (p * p) → Fin 2) :
    tOp s (fun r c => f (toMatrix x r c)) = tFlat s (f ∘ x) := rfl

lemma seg_triple_not_all_equiv {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) {i j k : ℕ} (hsum : i + j + k = p * p) :
    ¬ (GEquiv f g s (seg p i) (seg p j) ∧ GEquiv f g s (seg p j) (seg p k)) := by
  let N := p * p
  let x : Fin N → Fin 2 := segTuple p i
  let y : Fin N → Fin 2 := segTuple p j ∘ (finRotate N)^[j + k]
  let z : Fin N → Fin 2 := segTuple p k ∘ (finRotate N)^[k]
  have htcyc : IsCyclic (tFlat s) := lemma_8_8 s hcyc
  have hy_eq : tOp s (fun r c => f (toMatrix y r c)) = tOp s (fun r c => f (seg p j r c)) := by
    rw [tOp_toMatrix_comp, seg, tOp_toMatrix_comp]
    exact (isCyclic_iterate (tFlat s) htcyc (f ∘ segTuple p j) (j + k)).symm
  have hz_eq : tOp s (fun r c => f (toMatrix z r c)) = tOp s (fun r c => f (seg p k r c)) := by
    rw [tOp_toMatrix_comp, seg, tOp_toMatrix_comp]
    exact (isCyclic_iterate (tFlat s) htcyc (f ∘ segTuple p k) k).symm
  have hcover : IsCover (toMatrix x) (toMatrix y) (toMatrix z) := by
    intro r c
    let idx : Fin N := finProdFinEquiv (r, c)
    have hidx : idx.val < N := idx.isLt
    change (x idx).val + (y idx).val + (z idx).val = 1
    dsimp [x, y, z]
    rw [val_segTuple, val_segTuple, val_segTuple, val_finRotate_iterate, val_finRotate_iterate]
    rw [mod_eq_ite (by omega), mod_eq_ite (by omega)]
    split_ifs <;> omega
  have hnot := lemma_8_7 R f g hf hg s hs (toMatrix x) (toMatrix y) (toMatrix z) hcover
  rintro ⟨hij, hjk⟩
  apply hnot
  refine ⟨?_, ?_⟩
  · unfold GEquiv at hij ⊢
    rw [hy_eq]
    exact hij
  · unfold GEquiv at hjk ⊢
    rw [hy_eq, hz_eq]
    exact hjk

lemma fin2_dichotomy {a b c : Fin 2} (hne : a ≠ b) : c = a ∨ c = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

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

lemma seg_zero_eq_zeroMat (p : ℕ) : seg p 0 = zeroMat p := by
  ext r c
  simp [seg, toMatrix, segTuple, zeroMat]

lemma seg_sq_eq_oneMat (p : ℕ) : seg p (p * p) = oneMat p := by
  funext r c
  simp only [seg, toMatrix, segTuple, oneMat, (finProdFinEquiv (r, c)).isLt, if_true]

lemma card_filter_val_lt {N i : ℕ} (hi : i ≤ N) :
    (Finset.univ.filter (fun idx : Fin N => idx.val < i)).card = i := by
  have himg : Finset.image Fin.val (Finset.univ.filter (fun idx : Fin N => idx.val < i)) =
      Finset.range i := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨idx, hlt, rfl⟩
      exact hlt
    · intro hlt
      exact ⟨⟨m, lt_of_lt_of_le hlt hi⟩, hlt, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

lemma area_seg {p i : ℕ} (hi : i ≤ p * p) :
    area (seg p i) = (i : ℚ) / (p : ℚ) ^ 2 := by
  unfold area
  congr 1
  rw [← Fintype.sum_prod_type (f := fun x : Fin p × Fin p => ((seg p i x.1 x.2).val : ℚ))]
  have heq : (∑ x : Fin p × Fin p, ((seg p i x.1 x.2).val : ℚ)) =
      ∑ idx : Fin (p * p), ((segTuple p i idx).val : ℚ) :=
    Equiv.sum_comp finProdFinEquiv (fun idx => ((segTuple p i idx).val : ℚ))
  rw [heq]
  simp_rw [val_segTuple, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp [Finset.sum_boole, card_filter_val_lt hi]

end Lemma810Proof

theorem solution {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) :
    (∀ i, i ≤ p * p → IsTame f g s (seg p i)) ∧
    ¬ GEquiv f g s (seg p 0) (seg p (p * p)) := by
  obtain ⟨q, hq⟩ := Lemma810Proof.prime_sq_eq_three_mul_add_one hp hp3
  have hneq : ¬ GEquiv f g s (seg p q) (seg p (q + 1)) := by
    intro h
    exact Lemma810Proof.seg_triple_not_all_equiv R f g hf hg s hs hcyc (i := q) (j := q) (k := q + 1)
      (by omega) ⟨rfl, h⟩
  have hdich (m : ℕ) : GEquiv f g s (seg p m) (seg p q) ∨ GEquiv f g s (seg p m) (seg p (q + 1)) :=
    Lemma810Proof.fin2_dichotomy hneq
  have hind : ∀ d : ℕ, d ≤ q →
      GEquiv f g s (seg p (q - d)) (seg p q) ∧
      GEquiv f g s (seg p (q + 1 + d)) (seg p (q + 1)) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp [GEquiv]
    | succ d ih =>
      intro hd
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have h1 : GEquiv f g s (seg p (q - (d + 1))) (seg p q) := by
        rcases hdich (q - (d + 1)) with h | h
        · exact h
        · exfalso
          exact Lemma810Proof.seg_triple_not_all_equiv R f g hf hg s hs hcyc
            (i := q - (d + 1)) (j := q + 1) (k := q + 1 + d) (by omega) ⟨h, ih2.symm⟩
      have h2 : GEquiv f g s (seg p (q + 1 + (d + 1))) (seg p (q + 1)) := by
        rcases hdich (q + 1 + (d + 1)) with h | h
        · exfalso
          exact Lemma810Proof.seg_triple_not_all_equiv R f g hf hg s hs hcyc
            (i := q + 1 + (d + 1)) (j := q) (k := q - (d + 1)) (by omega) ⟨h, h1.symm⟩
        · exact h
      exact ⟨h1, h2⟩
  have h_le_q : ∀ i, i ≤ q → GEquiv f g s (seg p i) (seg p q) := by
    intro i hi
    have := (hind (q - i) (by omega)).1
    rwa [Nat.sub_sub_self hi] at this
  have h0_eq_q : GEquiv f g s (seg p 0) (seg p q) := h_le_q 0 (Nat.zero_le q)
  have h_gt_q : ∀ i, q + 1 ≤ i → i ≤ p * p → GEquiv f g s (seg p i) (seg p (q + 1)) := by
    intro i hi1 hi2
    by_cases hle : i ≤ 2 * q + 1
    · have := (hind (i - (q + 1)) (by omega)).2
      rwa [Nat.add_sub_of_le hi1] at this
    · rcases hdich i with h | h
      · exfalso
        have hsub : GEquiv f g s (seg p (p * p - i)) (seg p q) := h_le_q (p * p - i) (by omega)
        exact Lemma810Proof.seg_triple_not_all_equiv R f g hf hg s hs hcyc
          (i := i) (j := 0) (k := p * p - i) (by omega)
          ⟨h.trans h0_eq_q.symm, h0_eq_q.trans hsub.symm⟩
      · exact h
  have hsq_eq_q1 : GEquiv f g s (seg p (p * p)) (seg p (q + 1)) :=
    h_gt_q (p * p) (by omega) le_rfl
  have hp2_val : (p : ℚ) ^ 2 = 3 * (q : ℚ) + 1 := by
    have hq_rat : ((p * p : ℕ) : ℚ) = ((3 * q + 1 : ℕ) : ℚ) := by rw [hq]
    push_cast at hq_rat
    linarith
  have hp2_pos : (0 : ℚ) < (p : ℚ) ^ 2 := by linarith
  constructor
  · intro i hi
    by_cases hiq : i ≤ q
    · left
      refine ⟨?_, ?_⟩
      · rw [← Lemma810Proof.seg_zero_eq_zeroMat]
        exact (h_le_q i hiq).trans h0_eq_q.symm
      · rw [Lemma810Proof.area_seg hi, div_lt_iff₀ hp2_pos]
        have hiq_rat : (i : ℚ) ≤ (q : ℚ) := by exact_mod_cast hiq
        linarith
    · right
      have hi1 : q + 1 ≤ i := by omega
      refine ⟨?_, ?_⟩
      · rw [← Lemma810Proof.seg_sq_eq_oneMat]
        exact (h_gt_q i hi1 hi).trans hsq_eq_q1.symm
      · rw [Lemma810Proof.area_seg hi, lt_div_iff₀ hp2_pos]
        have hi1_rat : (q : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast hi1
        linarith
  · intro h0sq
    apply hneq
    exact h0_eq_q.symm.trans (h0sq.trans hsq_eq_q1)
