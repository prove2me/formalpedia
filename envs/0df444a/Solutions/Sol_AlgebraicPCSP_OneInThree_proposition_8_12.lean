-- Prove2me | solution 1 for AlgebraicPCSP.OneInThree.proposition_8_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:35:57.210991+00:00
-- url     : https://prove2.me/submissions/9b8c3a61-06cd-4363-9631-dbda263d01cc

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices

set_option autoImplicit false
set_option linter.unusedVariables false

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.OneInThree

namespace Prop812Proof

lemma ss_cover_cases : ∀ a b c : Fin 2, a.val + b.val + c.val = 1 →
    (![a, b, c] : Fin 3 → Fin 2) = ![1, 0, 0] ∨ (![a, b, c] : Fin 3 → Fin 2) = ![0, 1, 0] ∨
      (![a, b, c] : Fin 3 → Fin 2) = ![0, 0, 1] := by decide

lemma lemma_8_7_local {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (X Y Z : Fin p → Fin p → Fin 2) (hcover : IsCover X Y Z) :
    ¬ (GEquiv f g s X Y ∧ GEquiv f g s Y Z) := by
  rintro ⟨hXY, hYZ⟩
  have hrow : ∀ i j, (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) ∈ R := by
    intro i j
    have hmem : (![X i j, Y i j, Z i j] : Fin 3 → Fin 2) ∈ oneInThree.rel () :=
      ss_cover_cases (X i j) (Y i j) (Z i j) (hcover i j)
    have := hf () _ hmem
    have e : (f ∘ (![X i j, Y i j, Z i j] : Fin 3 → Fin 2)) =
        (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) := by
      ext k; fin_cases k <;> rfl
    rw [e] at this
    exact this
  have hcol : ∀ j, (fun c : Fin 3 => s (fun i : Fin p => (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) c)) ∈ R := by
    intro j
    exact hs () (fun i => (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D)) (fun i => hrow i j)
  have htot := hs () (fun j => fun c : Fin 3 => s (fun i : Fin p => (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) c)) hcol
  have hgt := hg () _ htot
  have e2 : (g ∘ fun c : Fin 3 => s (fun j : Fin p => (fun c : Fin 3 => s (fun i : Fin p => (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) c)) c)) =
      ![g (tOp s (fun i j => f (X i j))), g (tOp s (fun i j => f (Y i j))), g (tOp s (fun i j => f (Z i j)))] := by
    ext k; fin_cases k <;> rfl
  have hgt' : (![g (tOp s (fun i j => f (X i j))), g (tOp s (fun i j => f (Y i j))), g (tOp s (fun i j => f (Z i j)))] : Fin 3 → Fin 2) ∈ nae.rel () := by
    rw [← e2]; exact hgt
  unfold GEquiv at hXY hYZ
  rw [← hYZ, ← hXY] at hgt'
  obtain ⟨h0, h1⟩ := hgt'
  generalize g (tOp s (fun i j => f (X i j))) = a at h0 h1
  fin_cases a
  · exact h0 rfl
  · exact h1 rfl

lemma ss_val_finRotate (n : ℕ) (i : Fin n) :
    (finRotate n i).val = if i.val + 1 = n then 0 else i.val + 1 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : i = Fin.last n
    · subst h; simp
    · have : i.val + 1 ≠ n + 1 := by
        intro h'; apply h; ext; simpa using h'
      rw [if_neg h, if_neg this]

lemma ss_rot_e (p : ℕ) (hp : 0 < p) (i j : Fin p) :
    finRotate (p * p) (finProdFinEquiv (i, j)) =
      finProdFinEquiv ((if j.val + 1 = p then finRotate p i else i), finRotate p j) := by
  apply Fin.ext
  rw [ss_val_finRotate]
  simp only [finProdFinEquiv_apply_val]
  have hi := i.2
  have hj := j.2
  by_cases hjl : j.val + 1 = p
  · rw [if_pos hjl, ss_val_finRotate p j, if_pos hjl, ss_val_finRotate p i]
    by_cases hil : i.val + 1 = p
    · rw [if_pos hil]
      have : j.val + p * i.val + 1 = p * p := by
        have h2 : p * (i.val + 1) = p * i.val + p := by ring
        have h3 : p * (i.val + 1) = p * p := by rw [hil]
        omega
      rw [if_pos this]; simp
    · rw [if_neg hil]
      have h1 : p * (i.val + 1) < p * p := Nat.mul_lt_mul_of_pos_left (by omega) hp
      have : j.val + p * i.val + 1 ≠ p * p := by
        have : p * (i.val + 1) = p * i.val + p := by ring
        omega
      rw [if_neg this]
      have : p * (i.val + 1) = p * i.val + p := by ring
      omega
  · rw [if_neg hjl, ss_val_finRotate, if_neg hjl]
    have h1 : p * (i.val + 1) ≤ p * p := Nat.mul_le_mul_left p (by omega)
    have h2 : p * (i.val + 1) = p * i.val + p := by ring
    have : j.val + p * i.val + 1 ≠ p * p := by omega
    rw [if_neg this]
    omega

lemma lemma_8_8_local {D : Type} {p : ℕ} (s : (Fin p → D) → D) (hcyc : IsCyclic s) :
    IsCyclic (tFlat s) := by
  intro x
  unfold tFlat tOp toMatrix
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : (x ∘ finRotate (0 * 0)) = x := by
      funext k; exact absurd k.2 (by simp)
    rw [this]
  · set c : Fin p → D := fun j => s (fun i => x (finProdFinEquiv (i, j))) with hc
    have key : (fun j => s (fun i => (x ∘ finRotate (p * p)) (finProdFinEquiv (i, j)))) =
        c ∘ finRotate p := by
      funext j
      simp only [Function.comp, hc]
      by_cases hjl : j.val + 1 = p
      · have : ∀ i, x (finRotate (p * p) (finProdFinEquiv (i, j))) =
            (fun i' => x (finProdFinEquiv (i', finRotate p j))) (finRotate p i) := by
          intro i
          rw [ss_rot_e p hp, if_pos hjl]
        simp_rw [this]
        exact (hcyc (fun i' => x (finProdFinEquiv (i', finRotate p j)))).symm
      · have : ∀ i, x (finRotate (p * p) (finProdFinEquiv (i, j))) =
            x (finProdFinEquiv (i, finRotate p j)) := by
          intro i
          rw [ss_rot_e p hp, if_neg hjl]
        simp_rw [this]
    rw [key]
    exact hcyc c

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
  have htcyc : IsCyclic (tFlat s) := lemma_8_8_local s hcyc
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
  have hnot := lemma_8_7_local R f g hf hg s hs (toMatrix x) (toMatrix y) (toMatrix z) hcover
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

lemma lemma_8_10_local {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) :
    (∀ i, i ≤ p * p → IsTame f g s (seg p i)) ∧
    ¬ GEquiv f g s (seg p 0) (seg p (p * p)) := by
  obtain ⟨q, hq⟩ := prime_sq_eq_three_mul_add_one hp hp3
  have hneq : ¬ GEquiv f g s (seg p q) (seg p (q + 1)) := by
    intro h
    exact seg_triple_not_all_equiv R f g hf hg s hs hcyc (i := q) (j := q) (k := q + 1)
      (by omega) ⟨rfl, h⟩
  have hdich (m : ℕ) : GEquiv f g s (seg p m) (seg p q) ∨ GEquiv f g s (seg p m) (seg p (q + 1)) :=
    fin2_dichotomy hneq
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
          exact seg_triple_not_all_equiv R f g hf hg s hs hcyc
            (i := q - (d + 1)) (j := q + 1) (k := q + 1 + d) (by omega) ⟨h, ih2.symm⟩
      have h2 : GEquiv f g s (seg p (q + 1 + (d + 1))) (seg p (q + 1)) := by
        rcases hdich (q + 1 + (d + 1)) with h | h
        · exfalso
          exact seg_triple_not_all_equiv R f g hf hg s hs hcyc
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
        exact seg_triple_not_all_equiv R f g hf hg s hs hcyc
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
      · rw [← seg_zero_eq_zeroMat]
        exact (h_le_q i hiq).trans h0_eq_q.symm
      · rw [area_seg hi, div_lt_iff₀ hp2_pos]
        have hiq_rat : (i : ℚ) ≤ (q : ℚ) := by exact_mod_cast hiq
        linarith
    · right
      have hi1 : q + 1 ≤ i := by omega
      refine ⟨?_, ?_⟩
      · rw [← seg_sq_eq_oneMat]
        exact (h_gt_q i hi1 hi).trans hsq_eq_q1.symm
      · rw [area_seg hi, lt_div_iff₀ hp2_pos]
        have hi1_rat : (q : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast hi1
        linarith
  · intro h0sq
    apply hneq
    exact h0_eq_q.symm.trans (h0sq.trans hsq_eq_q1)

/-- Shorthand for an almost rectangle with `m` columns of height `k` and `p - m` columns of height `l`. -/
def rect (p k l m : ℕ) : Fin p → Fin p → Fin 2 :=
  colMatrix p (fun j => if j.val < m then k else l)

lemma sum_colMatrix_col {p : ℕ} (h : Fin p → ℕ) (hh : ∀ j, h j ≤ p) (j : Fin p) :
    (∑ i : Fin p, ((colMatrix p h i j).val : ℚ)) = (h j : ℚ) := by
  have hval : ∀ i : Fin p, ((colMatrix p h i j).val : ℚ) = if i.val < h j then 1 else 0 := by
    intro i
    unfold colMatrix
    split_ifs <;> rfl
  simp_rw [hval]
  simp [Finset.sum_boole, card_filter_val_lt (hh j)]

lemma area_rect {p k l m : ℕ} (hlk : l ≤ k) (hkp : k ≤ p) (hmp : m ≤ p) :
    area (rect p k l m) = ((m * k + (p - m) * l : ℕ) : ℚ) / (p : ℚ) ^ 2 := by
  unfold area rect
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

lemma colMatrix_shift {D : Type} {p : ℕ} (f : Fin 2 → D) (g : D → Fin 2)
    (s : (Fin p → D) → D) (hcyc : IsCyclic s) (h : Fin p → ℕ) (r : ℕ) :
    GEquiv f g s (colMatrix p (h ∘ (finRotate p)^[r])) (colMatrix p h) := by
  unfold GEquiv tOp colMatrix
  congr 1
  exact (isCyclic_iterate s hcyc (fun j => s (fun i => f (if i.val < h j then 1 else 0))) r).symm

lemma shift_two_blocks {p m a b : ℕ} (hm : m ≤ p) :
    ((fun j : Fin p => if j.val < m then a else b) ∘ (finRotate p)^[m]) =
      (fun j : Fin p => if j.val < p - m then b else a) := by
  ext j
  have hj : j.val < p := j.isLt
  dsimp [Function.comp]
  rw [val_finRotate_iterate, mod_eq_ite (by omega)]
  split_ifs <;> omega

lemma colMatrix_triple_not_all_equiv {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) (h₁ h₂ h₃ : Fin p → ℕ) (hsum : ∀ j : Fin p, h₁ j + h₂ j + h₃ j = p) :
    ¬ (GEquiv f g s (colMatrix p h₁) (colMatrix p h₂) ∧
       GEquiv f g s (colMatrix p h₂) (colMatrix p h₃)) := by
  let X : Fin p → Fin p → Fin 2 := colMatrix p h₁
  let Y : Fin p → Fin p → Fin 2 := fun i j => colMatrix p h₂ ((finRotate p)^[h₂ j + h₃ j] i) j
  let Z : Fin p → Fin p → Fin 2 := fun i j => colMatrix p h₃ ((finRotate p)^[h₃ j] i) j
  have hY : tOp s (fun i j => f (Y i j)) = tOp s (fun i j => f (colMatrix p h₂ i j)) := by
    unfold tOp
    congr 1
    ext j
    exact (isCyclic_iterate s hcyc (fun i => f (colMatrix p h₂ i j)) (h₂ j + h₃ j)).symm
  have hZ : tOp s (fun i j => f (Z i j)) = tOp s (fun i j => f (colMatrix p h₃ i j)) := by
    unfold tOp
    congr 1
    ext j
    exact (isCyclic_iterate s hcyc (fun i => f (colMatrix p h₃ i j)) (h₃ j)).symm
  have hcover : IsCover X Y Z := by
    intro i j
    have hi : i.val < p := i.isLt
    have hj := hsum j
    dsimp [X, Y, Z, colMatrix]
    have hv : ∀ b : Prop, [Decidable b] → (if b then (1 : Fin 2) else 0).val = if b then 1 else 0 := by
      intro b _; split_ifs <;> rfl
    rw [hv, hv, hv, val_finRotate_iterate, val_finRotate_iterate]
    rw [mod_eq_ite (by omega), mod_eq_ite (by omega)]
    split_ifs <;> omega
  have hnot := lemma_8_7_local R f g hf hg s hs X Y Z hcover
  rintro ⟨h12, h23⟩
  apply hnot
  refine ⟨?_, ?_⟩
  · unfold GEquiv at h12 ⊢
    rw [hY]
    exact h12
  · unfold GEquiv at h23 ⊢
    rw [hY, hZ]
    exact h23

lemma rect_succ_eq_seg {p l m : ℕ} (hl : l < p) (hm : m ≤ p) :
    rect p (l + 1) l m = seg p (p * l + m) := by
  ext i j
  have hi : i.val < p := i.isLt
  have hj : j.val < p := j.isLt
  unfold rect colMatrix seg toMatrix segTuple
  simp only [finProdFinEquiv_apply_val]
  have hiff : i.val < (if j.val < m then l + 1 else l) ↔ j.val + p * i.val < p * l + m := by
    rcases lt_trichotomy i.val l with hlt | rfl | hgt
    · have : p * (i.val + 1) ≤ p * l := Nat.mul_le_mul_left p (by omega)
      have : p * (i.val + 1) = p * i.val + p := by ring
      split_ifs <;> omega
    · split_ifs <;> omega
    · have : p * (l + 1) ≤ p * i.val := Nat.mul_le_mul_left p (by omega)
      have : p * (l + 1) = p * l + p := by ring
      split_ifs <;> omega
  by_cases h : i.val < (if j.val < m then l + 1 else l)
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (mt hiff.mpr h)]

lemma rect_step_le_one_tame {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) {k l m : ℕ} (hlk : l ≤ k) (hkp : k ≤ p) (hmp : m ≤ p) (hd : k - l ≤ 1) :
    IsTame f g s (rect p k l m) := by
  have hseg := (lemma_8_10_local R f g hf hg hp hp3 s hs hcyc).1
  by_cases hkl : k = l
  · subst hkl
    by_cases hlp : k = p
    · rw [hlp]
      have heq : rect p p p m = seg p (p * p) := by
        funext i j
        simp only [rect, colMatrix, seg, toMatrix, segTuple, i.isLt, (finProdFinEquiv (i, j)).isLt,
          ite_self, if_true]
      rw [heq]
      exact hseg (p * p) le_rfl
    · have hlt : k < p := by omega
      have heq : rect p k k m = rect p (k + 1) k 0 := by
        ext i j
        simp [rect, colMatrix]
      rw [heq, rect_succ_eq_seg hlt (Nat.zero_le p)]
      have hle : p * k + 0 ≤ p * p := by
        have : p * k ≤ p * p := Nat.mul_le_mul_left p (by omega)
        omega
      exact hseg (p * k + 0) hle
  · have hk_eq : k = l + 1 := by omega
    have hlt : l < p := by omega
    rw [hk_eq, rect_succ_eq_seg hlt hmp]
    have hle : p * l + m ≤ p * p := by
      calc p * l + m ≤ p * l + p := by omega
      _ = p * (l + 1) := by ring
      _ ≤ p * p := Nat.mul_le_mul_left p (by omega)
    exact hseg (p * l + m) hle

/-- Distance measure `|3N - (3q + 1)|` from the `1/3` boundary `p² = 3q + 1`. -/
def qdist (q N : ℕ) : ℕ :=
  if N ≤ q then 3 * q + 1 - 3 * N else 3 * N - (3 * q + 1)

lemma dist_double {q N N' : ℕ} (h : 2 * N + N' = 3 * q + 1) :
    qdist q N' = 2 * qdist q N ∧ 0 < qdist q N := by
  unfold qdist
  split_ifs <;> omega

lemma area_lt_one_third_iff {p q k l m : ℕ} (hq : p * p = 3 * q + 1)
    (hlk : l ≤ k) (hkp : k ≤ p) (hmp : m ≤ p) :
    area (rect p k l m) < 1 / 3 ↔ m * k + (p - m) * l ≤ q := by
  have hp2_val : (p : ℚ) ^ 2 = 3 * (q : ℚ) + 1 := by
    have hq_rat : ((p * p : ℕ) : ℚ) = ((3 * q + 1 : ℕ) : ℚ) := by rw [hq]
    push_cast at hq_rat
    linarith
  have hp2_pos : (0 : ℚ) < (p : ℚ) ^ 2 := by linarith
  rw [area_rect hlk hkp hmp, div_lt_iff₀ hp2_pos]
  constructor
  · intro hlt
    have hlt' : 3 * ((m * k + (p - m) * l : ℕ) : ℚ) < 3 * (q : ℚ) + 1 := by linarith
    have hnat : 3 * (m * k + (p - m) * l) < 3 * q + 1 := by exact_mod_cast hlt'
    omega
  · intro hle
    have hle' : ((m * k + (p - m) * l : ℕ) : ℚ) ≤ (q : ℚ) := by exact_mod_cast hle
    linarith

lemma one_third_lt_area_iff {p q k l m : ℕ} (hq : p * p = 3 * q + 1)
    (hlk : l ≤ k) (hkp : k ≤ p) (hmp : m ≤ p) :
    1 / 3 < area (rect p k l m) ↔ q + 1 ≤ m * k + (p - m) * l := by
  have hp2_val : (p : ℚ) ^ 2 = 3 * (q : ℚ) + 1 := by
    have hq_rat : ((p * p : ℕ) : ℚ) = ((3 * q + 1 : ℕ) : ℚ) := by rw [hq]
    push_cast at hq_rat
    linarith
  have hp2_pos : (0 : ℚ) < (p : ℚ) ^ 2 := by linarith
  rw [area_rect hlk hkp hmp, lt_div_iff₀ hp2_pos]
  constructor
  · intro hlt
    have hlt' : 3 * (q : ℚ) + 1 < 3 * ((m * k + (p - m) * l : ℕ) : ℚ) := by linarith
    have hnat : 3 * q + 1 < 3 * (m * k + (p - m) * l) := by exact_mod_cast hlt'
    omega
  · intro hle
    have hle' : (q : ℚ) + 1 ≤ ((m * k + (p - m) * l : ℕ) : ℚ) := by exact_mod_cast hle
    linarith

lemma rect_large_area_tame {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p q b d : ℕ} (hp12 : 12 < p) (hq : p * p = 3 * q + 1)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s)
    (h0_ne_1 : ¬ GEquiv f g s (zeroMat p) (oneMat p))
    (hd2 : 2 ≤ d) (hd_bound : d ≤ b)
    (ih_d : ∀ d' < d, d' ≤ b → ∀ k l m : ℕ, l ≤ k → k ≤ p → m ≤ p → k - l = d' →
      IsTame f g s (rect p k l m))
    {k l m : ℕ} (hlk : l ≤ k) (hkp : k ≤ p) (hmp : m ≤ p) (hkl : k - l = d)
    (h512 : 5 * (p * p) ≤ 12 * (m * k + (p - m) * l)) :
    IsTame f g s (rect p k l m) := by
  let k₁ := (p - l + 1) / 2
  let k₂ := (p - l) / 2
  let l₁ := (p - k + 1) / 2
  let l₂ := (p - k) / 2
  have hl₁k₁ : l₁ ≤ k₁ := by dsimp [l₁, k₁]; omega
  have hk₁p : k₁ ≤ p := by dsimp [k₁]; omega
  have hl₂k₂ : l₂ ≤ k₂ := by dsimp [l₂, k₂]; omega
  have hk₂p : k₂ ≤ p := by dsimp [k₂]; omega
  have hd₁_lt : k₁ - l₁ < d := by dsimp [k₁, l₁]; omega
  have hd₂_lt : k₂ - l₂ < d := by dsimp [k₂, l₂]; omega
  have htame₁ : IsTame f g s (rect p k₁ l₁ (p - m)) :=
    ih_d (k₁ - l₁) hd₁_lt (by omega) k₁ l₁ (p - m) hl₁k₁ hk₁p (by omega) rfl
  have htame₂ : IsTame f g s (rect p k₂ l₂ (p - m)) :=
    ih_d (k₂ - l₂) hd₂_lt (by omega) k₂ l₂ (p - m) hl₂k₂ hk₂p (by omega) rfl
  have hsum_k : k + l₁ + l₂ = p := by dsimp [l₁, l₂]; omega
  have hsum_l : l + k₁ + k₂ = p := by dsimp [k₁, k₂]; omega
  have hk_diff : k₁ ≤ k₂ + 1 := by dsimp [k₁, k₂]; omega
  have hl_diff : l₁ ≤ l₂ + 1 := by dsimp [l₁, l₂]; omega
  let N := m * k + (p - m) * l
  let N₁ := (p - m) * k₁ + m * l₁
  let N₂ := (p - m) * k₂ + m * l₂
  have hN_sum : N + N₁ + N₂ = p * p := by
    calc N + N₁ + N₂
      = m * (k + l₁ + l₂) + (p - m) * (l + k₁ + k₂) := by dsimp [N, N₁, N₂]; ring
    _ = m * p + (p - m) * p := by rw [hsum_k, hsum_l]
    _ = (m + (p - m)) * p := by ring
    _ = p * p := by rw [Nat.add_sub_of_le hmp]
  have hN₁_diff : N₁ ≤ N₂ + p := by
    calc (p - m) * k₁ + m * l₁
      ≤ (p - m) * (k₂ + 1) + m * (l₂ + 1) := by gcongr
    _ = ((p - m) * k₂ + m * l₂) + ((p - m) + m) := by ring
    _ = N₂ + p := by rw [Nat.sub_add_cancel hmp]
  have hN₂_le_N₁ : N₂ ≤ N₁ := by
    have : k₂ ≤ k₁ := by dsimp [k₁, k₂]; omega
    have : l₂ ≤ l₁ := by dsimp [l₁, l₂]; omega
    dsimp [N₁, N₂]
    gcongr
  have hp_lt_sq : 12 * p < p * p :=
    Nat.mul_lt_mul_of_pos_right hp12 (by omega)
  have hN₁_q : N₁ ≤ q := by omega
  have hN₂_q : N₂ ≤ q := by omega
  have harea₁ : area (rect p k₁ l₁ (p - m)) < 1 / 3 :=
    (area_lt_one_third_iff hq hl₁k₁ hk₁p (by omega)).mpr
      (by rw [Nat.sub_sub_self hmp]; exact hN₁_q)
  have harea₂ : area (rect p k₂ l₂ (p - m)) < 1 / 3 :=
    (area_lt_one_third_iff hq hl₂k₂ hk₂p (by omega)).mpr
      (by rw [Nat.sub_sub_self hmp]; exact hN₂_q)
  have hZ₁_0 : GEquiv f g s (rect p k₁ l₁ (p - m)) (zeroMat p) := by
    rcases htame₁ with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · exfalso; linarith
  have hZ₂_0 : GEquiv f g s (rect p k₂ l₂ (p - m)) (zeroMat p) := by
    rcases htame₂ with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · exfalso; linarith
  let hY₁ : Fin p → ℕ := fun j => if j.val < m then l₁ else k₁
  let hY₂ : Fin p → ℕ := fun j => if j.val < m then l₂ else k₂
  have hshift₁ : GEquiv f g s (rect p k₁ l₁ (p - m)) (colMatrix p hY₁) := by
    unfold rect
    rw [← shift_two_blocks hmp]
    exact colMatrix_shift f g s hcyc hY₁ m
  have hshift₂ : GEquiv f g s (rect p k₂ l₂ (p - m)) (colMatrix p hY₂) := by
    unfold rect
    rw [← shift_two_blocks hmp]
    exact colMatrix_shift f g s hcyc hY₂ m
  have hY₁_0 : GEquiv f g s (colMatrix p hY₁) (zeroMat p) := hshift₁.symm.trans hZ₁_0
  have hY₂_0 : GEquiv f g s (colMatrix p hY₂) (zeroMat p) := hshift₂.symm.trans hZ₂_0
  have hnot := colMatrix_triple_not_all_equiv R f g hf hg s hs hcyc
    (fun j => if j.val < m then k else l) hY₁ hY₂ (by
      intro j
      dsimp [hY₁, hY₂]
      split_ifs <;> omega)
  have hX_1 : GEquiv f g s (rect p k l m) (oneMat p) := by
    rcases fin2_dichotomy h0_ne_1 (c := g (tOp s (fun i j => f (rect p k l m i j)))) with h0 | h1
    · exfalso
      exact hnot ⟨h0.trans hY₁_0.symm, hY₁_0.trans hY₂_0.symm⟩
    · exact h1
  right
  refine ⟨hX_1, (one_third_lt_area_iff hq hlk hkp hmp).mpr ?_⟩
  change q + 1 ≤ N
  omega

lemma rect_step_Z_tame {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p q : ℕ} (hq : p * p = 3 * q + 1)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s)
    (h0_ne_1 : ¬ GEquiv f g s (zeroMat p) (oneMat p))
    {k l m k' l' m' : ℕ} (hlk : l ≤ k) (hkp : k ≤ p) (hmp : m ≤ p)
    (hl'k' : l' ≤ k') (hk'p : k' ≤ p) (hm'p : m' ≤ p)
    (hZ_fn : Fin p → ℕ)
    (hZ_shift : GEquiv f g s (rect p k' l' m') (colMatrix p hZ_fn))
    (hsum_Z : ∀ j : Fin p,
      (if j.val < m then k else l) +
      ((fun i : Fin p => if i.val < m then k else l) ((finRotate p)^[p - m] j)) +
      hZ_fn j = p)
    (hN' : 2 * (m * k + (p - m) * l) + (m' * k' + (p - m') * l') = p * p)
    (htame_Z' : IsTame f g s (rect p k' l' m')) :
    IsTame f g s (rect p k l m) := by
  let hX_fn : Fin p → ℕ := fun j => if j.val < m then k else l
  let hY_fn : Fin p → ℕ := hX_fn ∘ (finRotate p)^[p - m]
  have hXY_eq : GEquiv f g s (colMatrix p hY_fn) (rect p k l m) :=
    colMatrix_shift f g s hcyc hX_fn (p - m)
  have hnot := colMatrix_triple_not_all_equiv R f g hf hg s hs hcyc hX_fn hY_fn hZ_fn hsum_Z
  have hXZ_neq : ¬ GEquiv f g s (rect p k l m) (rect p k' l' m') := by
    intro hXZ
    exact hnot ⟨hXY_eq.symm, hXY_eq.trans (hXZ.trans hZ_shift)⟩
  rcases htame_Z' with ⟨hZ0, hareaZ⟩ | ⟨hZ1, hareaZ⟩
  · have hN'_q : m' * k' + (p - m') * l' ≤ q :=
      (area_lt_one_third_iff hq hl'k' hk'p hm'p).mp hareaZ
    have hN_gt : q + 1 ≤ m * k + (p - m) * l := by omega
    have hX1 : GEquiv f g s (rect p k l m) (oneMat p) := by
      rcases fin2_dichotomy h0_ne_1 (c := g (tOp s (fun i j => f (rect p k l m i j)))) with h0 | h1
      · exfalso; exact hXZ_neq (h0.trans hZ0.symm)
      · exact h1
    exact Or.inr ⟨hX1, (one_third_lt_area_iff hq hlk hkp hmp).mpr hN_gt⟩
  · have hN'_gt : q + 1 ≤ m' * k' + (p - m') * l' :=
      (one_third_lt_area_iff hq hl'k' hk'p hm'p).mp hareaZ
    have hN_q : m * k + (p - m) * l ≤ q := by omega
    have hX0 : GEquiv f g s (rect p k l m) (zeroMat p) := by
      rcases fin2_dichotomy h0_ne_1 (c := g (tOp s (fun i j => f (rect p k l m i j)))) with h0 | h1
      · exact h0
      · exfalso; exact hXZ_neq (h1.trans hZ1.symm)
    exact Or.inl ⟨hX0, (area_lt_one_third_iff hq hlk hkp hmp).mpr hN_q⟩

end Prop812Proof

theorem solution {D : Type} [Fintype D] [DecidableEq D] (R : Set (Fin 3 → D))
    (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (hp : p.Prime) (hpD : 60 * Fintype.card D < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) (X : Fin p → Fin p → Fin 2)
    (hX : IsAlmostRectangle (5 * Fintype.card D) X) :
    IsTame f g s X := by
  open Prop812Proof in
  have hD_pos : 0 < Fintype.card D := Fintype.card_pos_iff.mpr ⟨f 0⟩
  have hp3 : 3 < p := by omega
  have hp12 : 12 < p := by omega
  obtain ⟨q, hq⟩ := prime_sq_eq_three_mul_add_one hp hp3
  have h0_ne_1 : ¬ GEquiv f g s (zeroMat p) (oneMat p) := by
    rw [← seg_zero_eq_zeroMat, ← seg_sq_eq_oneMat]
    exact (lemma_8_10_local R f g hf hg hp hp3 s hs hcyc).2
  have h_step : ∀ d : ℕ, d ≤ 5 * Fintype.card D →
      ∀ k l m : ℕ, l ≤ k → k ≤ p → m ≤ p → k - l = d → IsTame f g s (rect p k l m) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih_d =>
      intro hd_bound
      by_cases hd1 : d ≤ 1
      · intro k l m hlk hkp hmp hkl
        exact rect_step_le_one_tame R f g hf hg hp hp3 s hs hcyc hlk hkp hmp (by omega)
      · have hd2 : 2 ≤ d := by omega
        have h_by_dist : ∀ u : ℕ, ∀ k l m : ℕ, l ≤ k → k ≤ p → m ≤ p → k - l = d →
            3 * q + 2 - qdist q (m * k + (p - m) * l) = u → IsTame f g s (rect p k l m) := by
          intro u
          induction u using Nat.strong_induction_on with
          | h u ih_u =>
            intro k l m hlk hkp hmp hkl hu
            let N := m * k + (p - m) * l
            change 3 * q + 2 - qdist q N = u at hu
            by_cases h512 : 5 * (p * p) ≤ 12 * N
            · exact rect_large_area_tame R f g hf hg hp12 hq s hs hcyc h0_ne_1
                hd2 hd_bound ih_d hlk hkp hmp hkl h512
            · have h512' : 12 * N < 5 * (p * p) := by omega
              have hdist_le : qdist q N ≤ 3 * q + 1 := by
                unfold qdist; split_ifs <;> omega
              have h2k_lt_p : 2 * k < p := by
                have hpk : p * k ≤ N + p * (5 * Fintype.card D) := by
                  calc p * k = m * k + (p - m) * k := by
                        rw [← Nat.add_mul, Nat.add_sub_of_le hmp]
                    _ ≤ m * k + (p - m) * (l + 5 * Fintype.card D) := by
                        gcongr; omega
                    _ = N + (p - m) * (5 * Fintype.card D) := by dsimp [N]; ring
                    _ ≤ N + p * (5 * Fintype.card D) := by gcongr; omega
                have h2pk : p * (2 * k) < p * p := by
                  have h6 : 6 * (p * (2 * k)) < 6 * (p * p) := by
                    calc 6 * (p * (2 * k)) = 12 * (p * k) := by ring
                      _ ≤ 12 * (N + p * (5 * Fintype.card D)) := by gcongr
                      _ = 12 * N + p * (60 * Fintype.card D) := by ring
                      _ < 5 * (p * p) + p * p :=
                        add_lt_add h512' (Nat.mul_lt_mul_of_pos_left hpD (by omega))
                      _ = 6 * (p * p) := by ring
                  omega
                exact lt_of_mul_lt_mul_left h2pk (by omega)
              by_cases h2m : 2 * m ≤ p
              · let k' := p - 2 * l
                let l' := p - k - l
                let m' := p - 2 * m
                let N' := m' * k' + (p - m') * l'
                let hZ_fn : Fin p → ℕ := fun j => if j.val < 2 * m then l' else k'
                have hZ_shift : GEquiv f g s (rect p k' l' m') (colMatrix p hZ_fn) := by
                  unfold rect
                  rw [← shift_two_blocks h2m]
                  exact colMatrix_shift f g s hcyc hZ_fn (2 * m)
                have hm'_sub : p - m' = 2 * m := by dsimp [m']; omega
                have hl'_eq : l' = p - (k + l) := by dsimp [l']; omega
                have hN' : 2 * N + N' = p * p := by
                  dsimp [N, N']
                  rw [hm'_sub, hl'_eq]
                  dsimp [k', m']
                  zify [h2m, hmp, (by omega : k + l ≤ p), (by omega : 2 * l ≤ p)]
                  ring
                have hdist := dist_double (q := q) (N := N) (N' := N') (by omega)
                have hu'_lt : 3 * q + 2 - qdist q N' < u := by omega
                have htame_Z' : IsTame f g s (rect p k' l' m') :=
                  ih_u (3 * q + 2 - qdist q N') hu'_lt k' l' m' (by omega) (by omega) (by omega)
                    (by omega) rfl
                refine rect_step_Z_tame R f g hf hg hq s hs hcyc h0_ne_1 hlk hkp hmp
                  (by omega) (by omega) (by omega) hZ_fn hZ_shift ?_ hN' htame_Z'
                intro j
                have hj : j.val < p := j.isLt
                dsimp [hZ_fn, k', l', Function.comp]
                rw [val_finRotate_iterate, mod_eq_ite (by omega)]
                split_ifs <;> omega
              · have h2m_gt : p < 2 * m := by omega
                have h2mp_le : 2 * m - p ≤ p := by omega
                let k' := p - k - l
                let l' := p - 2 * k
                let m' := p - (2 * m - p)
                let N' := m' * k' + (p - m') * l'
                let hZ_fn : Fin p → ℕ := fun j => if j.val < 2 * m - p then l' else k'
                have hZ_shift : GEquiv f g s (rect p k' l' m') (colMatrix p hZ_fn) := by
                  unfold rect
                  rw [← shift_two_blocks h2mp_le]
                  exact colMatrix_shift f g s hcyc hZ_fn (2 * m - p)
                have hm'_eq : m' = 2 * p - 2 * m := by dsimp [m']; omega
                have hm'_sub : p - m' = 2 * m - p := by dsimp [m']; omega
                have hk'_eq : k' = p - (k + l) := by dsimp [k']; omega
                have hN' : 2 * N + N' = p * p := by
                  dsimp [N, N']
                  rw [hm'_sub, hm'_eq, hk'_eq]
                  dsimp [l']
                  zify [(by omega : 2 * m ≤ 2 * p), (by omega : p ≤ 2 * m), hmp,
                    (by omega : k + l ≤ p), (by omega : 2 * k ≤ p)]
                  ring
                have hdist := dist_double (q := q) (N := N) (N' := N') (by omega)
                have hu'_lt : 3 * q + 2 - qdist q N' < u := by omega
                have htame_Z' : IsTame f g s (rect p k' l' m') :=
                  ih_u (3 * q + 2 - qdist q N') hu'_lt k' l' m' (by omega) (by omega) (by omega)
                    (by omega) rfl
                refine rect_step_Z_tame R f g hf hg hq s hs hcyc h0_ne_1 hlk hkp hmp
                  (by omega) (by omega) (by omega) hZ_fn hZ_shift ?_ hN' htame_Z'
                intro j
                have hj : j.val < p := j.isLt
                dsimp [hZ_fn, k', l', Function.comp]
                rw [val_finRotate_iterate, mod_eq_ite (by omega)]
                split_ifs <;> omega
        intro k l m hlk hkp hmp hkl
        exact h_by_dist (3 * q + 2 - qdist q (m * k + (p - m) * l)) k l m hlk hkp hmp hkl rfl
  rcases hX with ⟨k, l, m, hlk, hkp, hmp, hd, rfl⟩
  exact h_step (k - l) hd k l m hlk hkp hmp rfl
