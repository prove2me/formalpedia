-- Prove2me | solution 1 for AbelianCayleyHDX.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:00:29.59356+00:00
-- url     : https://prove2.me/submissions/500c9df4-ccc4-4322-abb4-827669f42e8f

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsSpanning
import Definitions.Def_AbelianCayleyHDX_HD
import Definitions.Def_AbelianCayleyHDX_rowWeight
import Definitions.Def_AbelianCayleyHDX_colWeight
import Definitions.Def_AbelianCayleyHDX_Htilde
import Definitions.Def_AbelianCayleyHDX_colGraph
import Definitions.Def_AbelianCayleyHDX_PD

namespace AbelianCayleyHDX.Sec3

/-! ### Characteristic two -/

lemma charP_two_of_card {F : Type*} [Field F] [Fintype F] (h : ℕ) (hh : 1 ≤ h)
    (hF : Fintype.card F = (2 ^ h) ^ 2) : CharP F 2 := by
  have h0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [hF] at h0
  push_cast at h0
  have h2 : (2 : F) = 0 := by
    rw [← pow_mul] at h0
    exact pow_eq_zero_iff (by omega) |>.1 h0
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2

/-! ### The triples `L_F` -/

section LFsec
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

lemma mem_LF {ℓ : Finset F} :
    ℓ ∈ LF F ↔ ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ ℓ = {a, b, a + b} := by
  simp only [LF, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩; exact ⟨a, b, ha, hb, hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩; exact ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩

lemma triple_card {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ({a, b, a + b} : Finset F).card = 3 := by
  rw [Finset.card_eq_three]
  exact ⟨a, b, a + b, hab, by intro h; grind, by intro h; grind, rfl⟩

lemma LF_card {ℓ : Finset F} (h : ℓ ∈ LF F) : ℓ.card = 3 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_LF.1 h
  exact triple_card ha hb hab

lemma LF_ne_zero {ℓ : Finset F} (h : ℓ ∈ LF F) {p : F} (hp : p ∈ ℓ) : p ≠ 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_LF.1 h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact ha
  · exact hb
  · intro h0; grind

lemma LF_eq {ℓ : Finset F} (h : ℓ ∈ LF F) {p r : F} (hp : p ∈ ℓ) (hr : r ∈ ℓ) (hpr : p ≠ r) :
    ℓ = {p, r, p + r} := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_LF.1 h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hr
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> grind

lemma triple_mem_LF {p r : F} (hp : p ≠ 0) (hr : r ≠ 0) (hpr : p ≠ r) :
    ({p, r, p + r} : Finset F) ∈ LF F := mem_LF.2 ⟨p, r, hp, hr, hpr, rfl⟩

lemma LF_sum {ℓ : Finset F} (h : ℓ ∈ LF F) : ∑ x ∈ ℓ, x = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_LF.1 h
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; grind),
    Finset.sum_pair (by grind)]
  grind

lemma LF_sum_sq {ℓ : Finset F} (h : ℓ ∈ LF F) : ∑ x ∈ ℓ, x ^ 2 = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_LF.1 h
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; grind),
    Finset.sum_pair (by grind)]
  grind

/-- Each nonzero `p` lies in `(|F| - 2)/2` triples. -/
lemma card_LF_through {p : F} (hp : p ≠ 0) :
    2 * ((LF F).filter (fun ℓ => p ∈ ℓ)).card = Fintype.card F - 2 := by
  set S : Finset F := Finset.univ.filter fun r => r ≠ 0 ∧ r ≠ p
  have hS : S.card = Fintype.card F - 2 := by
    have : S = (Finset.univ.erase 0).erase p := by
      ext r; simp [S, and_comm]
    rw [this, Finset.card_erase_of_mem (by simp [hp]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ]
    omega
  rw [← hS, Finset.card_eq_sum_card_fiberwise (f := fun r => ({p, r, p + r} : Finset F))
    (t := (LF F).filter (fun ℓ => p ∈ ℓ))]
  · rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    simp only [Finset.mem_filter] at hℓ
    have : S.filter (fun r => ({p, r, p + r} : Finset F) = ℓ) = ℓ.erase p := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, S]
      constructor
      · rintro ⟨⟨hr0, hrp⟩, rfl⟩; exact ⟨hrp, by simp⟩
      · rintro ⟨hrp, hr⟩
        exact ⟨⟨LF_ne_zero hℓ.1 hr, hrp⟩, (LF_eq hℓ.1 hℓ.2 hr (Ne.symm hrp)).symm⟩
    rw [this, Finset.card_erase_of_mem hℓ.2, LF_card hℓ.1]
  · intro r hr
    have hr2 : r ≠ 0 ∧ r ≠ p := (Finset.mem_filter.1 hr).2
    exact Finset.mem_filter.2 ⟨triple_mem_LF hp hr2.1 (Ne.symm hr2.2), by simp⟩

end LFsec

/-! ### Generic incidence counting for weight-three matrices -/

section Gram
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ (ZMod 2))

lemma z2_ne_zero_iff (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by revert a; decide

/-- Columns `i ≠ j` sharing a row. -/
def Adj' (i j : κ) : Prop := i ≠ j ∧ ∃ r : ι, H r i = 1 ∧ H r j = 1

variable {H} {ρ : ℕ} (hrow : ∀ r, rowWeight H r = 3) (hcol : ∀ c, colWeight H c = ρ)
  (hpair : ∀ i j : κ, i ≠ j →
    (Finset.univ.filter fun r : ι => H r i = 1 ∧ H r j = 1).card ≤ 1)

include hpair in
lemma rows_eq' {r r' : ι} {i j : κ} (hij : i ≠ j) (hi : H r i = 1) (hj : H r j = 1)
    (hi' : H r' i = 1) (hj' : H r' j = 1) : r = r' := by
  have := Finset.card_le_one.1 (hpair i j hij) r (by simp [hi, hj]) r' (by simp [hi', hj'])
  exact this

lemma supp_eq (r : ι) : (Finset.univ.filter fun c => H r c ≠ 0) =
    Finset.univ.filter fun c => H r c = 1 := by
  ext c; simp [z2_ne_zero_iff]

include hrow hcol hpair in
open Classical in
lemma card_adj' (i : κ) : (Finset.univ.filter fun j => Adj' H i j).card = 2 * ρ := by
  have hrows : (Finset.univ.filter fun r : ι => H r i = 1).card = ρ := by
    rw [← hcol i, colWeight]; congr 1; ext r; simp [z2_ne_zero_iff]
  have heq : (Finset.univ.filter fun j => Adj' H i j) =
      (Finset.univ.filter fun r : ι => H r i = 1).biUnion
        fun r => (Finset.univ.filter fun c => H r c = 1).erase i := by
    ext j
    rw [Finset.mem_filter, Finset.mem_biUnion]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_erase]
    unfold Adj'
    constructor
    · rintro ⟨hij, r, hi, hj⟩; exact ⟨r, hi, Ne.symm hij, hj⟩
    · rintro ⟨r, hi, hji, hj⟩; exact ⟨Ne.symm hji, r, hi, hj⟩
  rw [heq, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (g := fun _ => 2)]
    · simp [hrows, mul_comm]
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Finset.card_erase_of_mem (by simp [hr]), ← supp_eq]
      have := hrow r; rw [rowWeight] at this; rw [this]
  · intro r hr r' hr' hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hr hr'
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    exact hne (rows_eq' hpair (Ne.symm hj.1) hr hj.2 hr' hj'.2)

include hcol hpair in
open Classical in
lemma gram' (i j : κ) :
    ((Htilde H).transpose * Htilde H - (ρ : ℝ) • (1 : Matrix κ κ ℝ)) i j =
      if Adj' H i j then 1 else 0 := by
  have hval : ∀ r c, ((H r c).val : ℝ) = if H r c = 1 then 1 else 0 := by
    intro r c
    by_cases h : H r c = 1
    · rw [if_pos h, h]; simp [ZMod.val_one]
    · rw [if_neg h]
      have : H r c = 0 := by by_contra h'; exact h ((z2_ne_zero_iff _).1 h')
      simp [this]
  have hsum : ∀ i j : κ, ((Htilde H).transpose * Htilde H) i j =
      ((Finset.univ.filter fun r : ι => H r i = 1 ∧ H r j = 1).card : ℝ) := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Htilde, Matrix.of_apply, hval]
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl (fun r _ => ?_)
    by_cases h1 : H r i = 1 <;> by_cases h2 : H r j = 1 <;> simp [h1, h2]
  rw [Matrix.sub_apply, hsum, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    have hrows : (Finset.univ.filter fun r : ι => H r i = 1).card = ρ := by
      rw [← hcol i, colWeight]; congr 1; ext r; simp [z2_ne_zero_iff]
    simp only [and_self, if_true, smul_eq_mul, mul_one, hrows]
    rw [if_neg (fun h => h.1 rfl)]; ring
  · simp only [hij, if_false, smul_eq_mul, mul_zero, sub_zero]
    by_cases hn : Adj' H i j
    · rw [if_pos hn]
      obtain ⟨-, r, hi, hj⟩ := hn
      have : (Finset.univ.filter fun r : ι => H r i = 1 ∧ H r j = 1) = {r} := by
        ext r'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hi', hj'⟩; exact (rows_eq' hpair hij hi hj hi' hj').symm
        · rintro rfl; exact ⟨hi, hj⟩
      rw [this]; simp
    · rw [if_neg hn]
      have : (Finset.univ.filter fun r : ι => H r i = 1 ∧ H r j = 1) = ∅ := by
        ext r'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hi', hj'⟩; exact hn ⟨hij, r', hi', hj'⟩
      rw [this]; simp

omit [DecidableEq κ] in
lemma sum_rowWeight_eq :
    ∑ r, rowWeight H r = ∑ c, colWeight H c := by
  simp only [rowWeight, colWeight, Finset.card_filter]
  exact Finset.sum_comm

end Gram

/-! ### The matrix `H_D` -/

section HDsec
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] {t : ℕ}
  (D : Finset (PG t F))

lemma HD_eq_one_iff (r : RowIdx D) (c : Omega F t) :
    HD D r c = 1 ↔ (c.1 : F) ∈ r.2.2.1 ∧ c.2 = r.2.1 + (c.1 : F) • r.1.1 := by
  unfold HD; split_ifs with h <;> simp [h]

lemma HD_ne_zero_iff (r : RowIdx D) (c : Omega F t) :
    HD D r c ≠ 0 ↔ (c.1 : F) ∈ r.2.2.1 ∧ c.2 = r.2.1 + (c.1 : F) • r.1.1 := by
  rw [z2_ne_zero_iff, HD_eq_one_iff]

lemma rowWeight_HD (r : RowIdx D) : rowWeight (HD D) r = 3 := by
  unfold rowWeight
  simp_rw [HD_ne_zero_iff]
  rw [← LF_card r.2.2.2]
  apply Finset.card_bij (fun c _ => (c.1 : F))
  · intro c hc; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc; exact hc.1
  · intro c hc c' hc' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    have h1 : c.1 = c'.1 := Units.ext h
    exact Prod.ext h1 (by rw [hc.2, hc'.2, h])
  · intro p hp
    have hp0 := LF_ne_zero r.2.2.2 hp
    refine ⟨(Units.mk0 p hp0, r.2.1 + p • r.1.1), ?_, rfl⟩
    simp [hp]

lemma colWeight_HD (c : Omega F t) :
    2 * colWeight (HD D) c = (Fintype.card F - 2) * (Dhat D).card := by
  unfold colWeight
  simp_rw [HD_ne_zero_iff]
  have hp0 : (c.1 : F) ≠ 0 := c.1.ne_zero
  have key : (Finset.univ.filter fun r : RowIdx D =>
      (c.1 : F) ∈ r.2.2.1 ∧ c.2 = r.2.1 + (c.1 : F) • r.1.1).card =
      (Dhat D).card * ((LF F).filter (fun ℓ => (c.1 : F) ∈ ℓ)).card := by
    rw [← Finset.card_attach (s := Dhat D),
      ← Finset.card_attach (s := (LF F).filter (fun ℓ => (c.1 : F) ∈ ℓ)), ← Finset.card_product]
    symm
    apply Finset.card_bij (fun (bℓ : {b // b ∈ Dhat D} × {ℓ // ℓ ∈ (LF F).filter
        (fun ℓ => (c.1 : F) ∈ ℓ)}) _ =>
      ((bℓ.1, c.2 + (c.1 : F) • bℓ.1.1,
        ⟨bℓ.2.1, (Finset.mem_filter.1 bℓ.2.2).1⟩) : RowIdx D))
    · rintro ⟨b, ℓ⟩ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(Finset.mem_filter.1 ℓ.2).2, ?_⟩
      ext k; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; grind
    · rintro ⟨b, ℓ⟩ _ ⟨b', ℓ'⟩ _ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, -, h3⟩ := h
      simp only [Prod.mk.injEq]
      exact ⟨h1, Subtype.ext h3⟩
    · rintro ⟨b, x, ℓ⟩ hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      refine ⟨(b, ⟨ℓ.1, Finset.mem_filter.2 ⟨ℓ.2, hr.1⟩⟩), Finset.mem_univ _, ?_⟩
      refine Prod.ext rfl (Prod.ext ?_ (Subtype.ext rfl))
      show c.2 + (c.1 : F) • b.1 = x
      rw [hr.2]; ext k; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; grind
  rw [key, mul_comm (Dhat D).card, ← mul_assoc, card_LF_through hp0]

lemma pair_HD {c c' : Omega F t} (hcc : c ≠ c') :
    (Finset.univ.filter fun r : RowIdx D => HD D r c = 1 ∧ HD D r c' = 1).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro r hr r' hr'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, HD_eq_one_iff] at hr hr'
  obtain ⟨⟨hp, hy⟩, ⟨hp', hy'⟩⟩ := hr
  obtain ⟨⟨hq, hz⟩, ⟨hq', hz'⟩⟩ := hr'
  have hne : (c.1 : F) ≠ (c'.1 : F) := by
    intro h
    apply hcc
    have h1 : c.1 = c'.1 := Units.ext h
    exact Prod.ext h1 (by rw [hy, hy', h])
  have hsum : (c.1 : F) + c'.1 ≠ 0 := by intro h0; apply hne; grind
  -- the direction is determined
  have hb : r.1.1 = r'.1.1 := by
    ext k
    have e1 := congrFun hy k; have e2 := congrFun hy' k
    have e3 := congrFun hz k; have e4 := congrFun hz' k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
    have : ((c.1 : F) + c'.1) * r.1.1 k = ((c.1 : F) + c'.1) * r'.1.1 k := by grind
    exact mul_left_cancel₀ hsum this
  have hx : r.2.1 = r'.2.1 := by
    ext k
    have e1 := congrFun hy k; have e3 := congrFun hz k
    have e5 := congrFun hb k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e3 e5
    grind
  have hℓ : r.2.2.1 = r'.2.2.1 := by
    rw [LF_eq r.2.2.2 hp hp' hne, LF_eq r'.2.2.2 hq hq' hne]
  obtain ⟨⟨b, hb'⟩, x, ⟨ℓ, hℓ'⟩⟩ := r
  obtain ⟨⟨b', hb''⟩, x', ⟨ℓ', hℓ''⟩⟩ := r'
  simp only at hb hx hℓ
  subst hb hx hℓ
  rfl

end HDsec

end AbelianCayleyHDX.Sec3


namespace AbelianCayleyHDX.Sec3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] {t : ℕ}
  (D : Finset (PG t F))

lemma HD_injective : Function.Injective (HD D) := by
  intro r r' hrr
  obtain ⟨p, hp, p', hp', hpp⟩ : ∃ p ∈ r.2.2.1, ∃ p' ∈ r.2.2.1, p ≠ p' := by
    have : 1 < r.2.2.1.card := by rw [LF_card r.2.2.2]; norm_num
    exact Finset.one_lt_card.1 this
  have hp0 := LF_ne_zero r.2.2.2 hp
  have hp0' := LF_ne_zero r.2.2.2 hp'
  let c : Omega F t := (Units.mk0 p hp0, r.2.1 + p • r.1.1)
  let c' : Omega F t := (Units.mk0 p' hp0', r.2.1 + p' • r.1.1)
  have hc : HD D r c = 1 := (HD_eq_one_iff D r c).2 ⟨hp, rfl⟩
  have hc' : HD D r c' = 1 := (HD_eq_one_iff D r c').2 ⟨hp', rfl⟩
  have hcc : c ≠ c' := by
    intro h; apply hpp; have := congrArg (fun z : Omega F t => (z.1 : F)) h; simpa [c, c'] using this
  have hr'c : HD D r' c = 1 := by rw [← hrr]; exact hc
  have hr'c' : HD D r' c' = 1 := by rw [← hrr]; exact hc'
  classical
  exact Finset.card_le_one.1 (pair_HD D hcc) r (by simp [hc, hc']) r' (by simp [hr'c, hr'c'])

end AbelianCayleyHDX.Sec3

open AbelianCayleyHDX AbelianCayleyHDX.Sec3 in
open Classical in
theorem solution (h : ℕ) (hq : 8 ≤ 2 ^ h) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = (2 ^ h) ^ 2) {t : ℕ} (ht : 1 ≤ t) (D : Finset (PG t F))
    (hD : IsSpanning D) :
    6 * Fintype.card (RowIdx D) = ((2 ^ h) ^ 2 - 2) * (Dhat D).card * Fintype.card (Omega F t) ∧
    Function.Injective (HD D) ∧
    (∀ r, rowWeight (HD D) r = 3) ∧
    (∀ c, 2 * colWeight (HD D) c = ((2 ^ h) ^ 2 - 2) * (Dhat D).card) ∧
    (∀ c c' : Omega F t, c ≠ c' →
      (Finset.univ.filter fun r => HD D r c = 1 ∧ HD D r c' = 1).card ≤ 1) ∧
    (∀ ρ : ℕ, 2 * ρ = ((2 ^ h) ^ 2 - 2) * (Dhat D).card →
      (colGraph D).IsRegularOfDegree (2 * ρ) ∧
      (Htilde (HD D)).transpose * Htilde (HD D) - (ρ : ℝ) • (1 : Matrix (Omega F t) (Omega F t) ℝ) =
        (colGraph D).adjMatrix ℝ ∧
      PD D = (1 / (2 * (ρ : ℝ))) • (colGraph D).adjMatrix ℝ) := by
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · norm_num at hq
    · exact hpos
  haveI : CharP F 2 := charP_two_of_card h hh hF
  have hcol : ∀ c, 2 * colWeight (HD D) c = ((2 ^ h) ^ 2 - 2) * (Dhat D).card := by
    intro c; rw [colWeight_HD, hF]
  have hpair : ∀ c c' : Omega F t, c ≠ c' →
      (Finset.univ.filter fun r => HD D r c = 1 ∧ HD D r c' = 1).card ≤ 1 := by
    intro c c' hcc
    convert pair_HD D hcc
  refine ⟨?_, HD_injective D, rowWeight_HD D, hcol, hpair, ?_⟩
  · have hs := sum_rowWeight_eq (H := HD D)
    simp only [rowWeight_HD, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
    have : 2 * ∑ c, colWeight (HD D) c =
        ∑ _c : Omega F t, ((2 ^ h) ^ 2 - 2) * (Dhat D).card := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun c _ => hcol c)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
    rw [← hs] at this
    linarith
  · intro ρ hρ
    have hcolρ : ∀ c, colWeight (HD D) c = ρ := by intro c; have := hcol c; omega
    have hpair' : ∀ i j : Omega F t, i ≠ j →
        (Finset.univ.filter fun r : RowIdx D => HD D r i = 1 ∧ HD D r j = 1).card ≤ 1 := by
      intro i j hij; convert pair_HD D hij
    have hgram : (Htilde (HD D)).transpose * Htilde (HD D) -
        (ρ : ℝ) • (1 : Matrix (Omega F t) (Omega F t) ℝ) = (colGraph D).adjMatrix ℝ := by
      ext i j
      rw [gram' hcolρ hpair', SimpleGraph.adjMatrix_apply]
      rfl
    refine ⟨?_, hgram, ?_⟩
    · intro v
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
      rw [← card_adj' (rowWeight_HD D) hcolρ hpair' v]
      rfl
    · unfold PD
      have : (Fintype.card F - 2) * (Dhat D).card / 2 = ρ := by rw [hF, ← hρ]; omega
      rw [this]
      unfold PH
      rw [hgram]
