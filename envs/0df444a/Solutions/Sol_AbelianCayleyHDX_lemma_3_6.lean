-- Prove2me | solution 1 for AbelianCayleyHDX.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:03:35.31208+00:00
-- url     : https://prove2.me/submissions/5d21fa17-3489-4ae2-8a06-41b711d1f916

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsSpanning
import Definitions.Def_AbelianCayleyHDX_HD
import Definitions.Def_AbelianCayleyHDX_rowWeight
import Definitions.Def_AbelianCayleyHDX_colWeight
import Definitions.Def_AbelianCayleyHDX_Htilde
import Definitions.Def_AbelianCayleyHDX_colGraph
import Definitions.Def_AbelianCayleyHDX_PD
import Definitions.Def_AbelianCayleyHDX_affineSpace
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_rowspan
import Definitions.Def_AbelianCayleyHDX_MinDistAtLeast3
import Definitions.Def_AbelianCayleyHDX_Phi

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

section Trace
variable {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]

lemma tr_nondeg {a : F} (ha : a ≠ 0) : ∃ b : F, Algebra.trace (ZMod 2) F (a * b) ≠ 0 := by
  have htr := (traceForm_nondegenerate (ZMod 2) F).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

variable {t : ℕ}

lemma Phi_apply (u : (Fin t → F) → F) (c : Omega F t) :
    Phi u c = Algebra.trace (ZMod 2) F ((c.1 : F) * u c.2) := rfl

lemma Phi_add' (u v : (Fin t → F) → F) : Phi (u + v) = Phi u + Phi v := by
  funext c; simp only [Phi_apply, Pi.add_apply, mul_add, map_add]

lemma Phi_sub' (u v : (Fin t → F) → F) : Phi (u - v) = Phi u - Phi v := by
  funext c; simp only [Phi_apply, Pi.sub_apply, mul_sub, map_sub]

lemma Phi_eq_zero {u : (Fin t → F) → F} (h : Phi u = 0) : u = 0 := by
  funext x
  by_contra hx
  obtain ⟨b, hb⟩ := tr_nondeg hx
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have := congrFun h (Units.mk0 b hb0, x)
  simp only [Phi_apply, Units.val_mk0, Pi.zero_apply] at this
  apply hb; rw [mul_comm]; exact this

end Trace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {t : ℕ}

lemma affine_of_mem_Dhat {D : Finset (PG t F)} {u : (Fin t → F) → F} (hu : u ∈ affineSpace D)
    {b : Fin t → F} (hb : b ∈ Dhat D) (x : Fin t → F) :
    ∃ A B : F, ∀ α : F, u (x + α • b) = A + B * α := by
  classical
  simp only [Dhat, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  obtain ⟨hb0, hbD⟩ := hb
  obtain ⟨A, B, hAB⟩ := hu _ hbD x
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep F b hb0
  refine ⟨A, B * (c : F)⁻¹, fun α => ?_⟩
  have := hAB (α * (c : F)⁻¹)
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have e : α * (c : F)⁻¹ * (c : F) = α := by field_simp
  rw [← hc, Units.smul_def, smul_smul, e] at this
  rw [this]; ring

lemma globally_affine_mem (D : Finset (PG t F)) (C : F) (a : Module.Dual F (Fin t → F)) :
    (fun x => C + a x) ∈ affineSpace D := by
  intro d _ x
  refine ⟨C + a x, a d.rep, fun α => ?_⟩
  simp only [map_add, map_smul, smul_eq_mul]; ring

variable [CharP F 2]

lemma mulVec_Phi (D : Finset (PG t F)) (u : (Fin t → F) → F) (r : RowIdx D) :
    (HD D).mulVec (Phi u) r =
      ∑ p ∈ r.2.2.1, Algebra.trace (ZMod 2) F (p * u (r.2.1 + p • r.1.1)) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  have h01 : ∀ c, HD D r c * Phi u c = if HD D r c = 1 then Phi u c else 0 := by
    intro c; unfold HD; split_ifs <;> simp_all
  simp_rw [h01]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun c _ => (c.1 : F))
  · intro c hc; simp only [Finset.mem_filter, Finset.mem_univ, true_and, HD_eq_one_iff] at hc
    exact hc.1
  · intro c hc c' hc' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HD_eq_one_iff] at hc hc'
    have h1 : c.1 = c'.1 := Units.ext h
    exact Prod.ext h1 (by rw [hc.2, hc'.2, h])
  · intro p hp
    have hp0 := LF_ne_zero r.2.2.2 hp
    refine ⟨(Units.mk0 p hp0, r.2.1 + p • r.1.1), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HD_eq_one_iff]
    exact ⟨hp, rfl⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HD_eq_one_iff] at hc
    rw [Phi_apply, hc.2]

lemma Phi_mem_ker {D : Finset (PG t F)} {u : (Fin t → F) → F} (hu : u ∈ affineSpace D) :
    Phi u ∈ kerF2 (HD D) := by
  unfold kerF2
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext r
  rw [mulVec_Phi, Pi.zero_apply]
  obtain ⟨A, B, hAB⟩ := affine_of_mem_Dhat hu r.1.2 r.2.1
  simp_rw [hAB]
  rw [← map_sum]
  have : ∑ p ∈ r.2.2.1, p * (A + B * p) = A * ∑ p ∈ r.2.2.1, p + B * ∑ p ∈ r.2.2.1, p ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => by ring)
  rw [this, LF_sum r.2.2.2, LF_sum_sq r.2.2.2]; simp

/-- Row space vectors are orthogonal to kernel vectors. -/
lemma dot_eq_zero {D : Finset (PG t F)} {v w : Omega F t → ZMod 2} (hv : v ∈ rowspan (HD D))
    (hw : w ∈ kerF2 (HD D)) : ∑ c, v c * w c = 0 := by
  unfold kerF2 at hw
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    have := congrFun hw r
    simpa [Matrix.mulVec, dotProduct] using this
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hx, hy,
      add_zero]
  | smul a x _ hx => simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hx,
      mul_zero]

lemma separate {c c' : Omega F t} (hcc : c ≠ c') : ∃ (C : F) (a : Module.Dual F (Fin t → F)),
    Phi (fun x => C + a x) c ≠ Phi (fun x => C + a x) c' := by
  by_cases h1 : (c.1 : F) = c'.1
  · have h2 : c.2 ≠ c'.2 := by
      intro h2; apply hcc; exact Prod.ext (Units.ext h1) h2
    have hsub : c.2 - c'.2 ≠ 0 := sub_ne_zero.2 h2
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual F (Fin t → F), f (c.2 - c'.2) ≠ 0 := by
      by_contra! hall
      exact hsub ((Module.forall_dual_apply_eq_zero_iff F _).1 hall)
    obtain ⟨z, hz⟩ := tr_nondeg c.1.ne_zero
    refine ⟨0, (z / f (c.2 - c'.2)) • f, ?_⟩
    intro h
    simp only [Phi_apply, zero_add, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← sub_eq_zero, ← map_sub, ← h1, ← mul_sub, ← mul_sub, ← map_sub] at h
    field_simp at h
    exact hz h
  · have hsub : (c.1 : F) - c'.1 ≠ 0 := sub_ne_zero.2 h1
    obtain ⟨z, hz⟩ := tr_nondeg hsub
    refine ⟨z, 0, ?_⟩
    intro h
    simp only [Phi_apply, LinearMap.zero_apply, add_zero] at h
    rw [← sub_eq_zero, ← map_sub, ← sub_mul] at h
    exact hz h

lemma nonzero_at (c : Omega F t) : ∃ (C : F) (a : Module.Dual F (Fin t → F)),
    Phi (fun x => C + a x) c ≠ 0 := by
  obtain ⟨z, hz⟩ := tr_nondeg c.1.ne_zero
  exact ⟨z, 0, by simpa [Phi_apply] using hz⟩

lemma minDist (D : Finset (PG t F)) : MinDistAtLeast3 (rowspan (HD D)) := by
  intro v hv hne
  by_contra hlt
  push Not at hlt
  set S := Finset.univ.filter fun i => v i ≠ 0 with hS
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hne; funext i; by_contra hi
    have : i ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; simpa using hi
    rw [h] at this; simp at this
  have hv1 : ∀ i ∈ S, v i = 1 := by
    intro i hi; simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact (z2_ne_zero_iff _).1 hi
  have hdot : ∀ w ∈ kerF2 (HD D), ∑ i ∈ S, w i = 0 := by
    intro w hw
    have := dot_eq_zero hv hw
    rw [← Finset.sum_filter_ne_zero] at this
    have e : (Finset.univ.filter fun i => v i * w i ≠ 0) ⊆ S := by
      intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      intro h0; apply hi; rw [h0, zero_mul]
    rw [Finset.sum_subset e] at this
    · rw [← this]; refine Finset.sum_congr rfl (fun i hi => ?_); rw [hv1 i hi, one_mul]
    · intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi; exact hi
  interval_cases hc : S.card
  · exact absurd (Finset.card_pos.2 hSne) (by omega)
  · obtain ⟨c, hc1⟩ := Finset.card_eq_one.1 hc
    obtain ⟨C, a, hCa⟩ := nonzero_at c
    have := hdot _ (Phi_mem_ker (globally_affine_mem D C a))
    rw [hc1, Finset.sum_singleton] at this
    exact hCa this
  · obtain ⟨c, c', hcc, hc2⟩ := Finset.card_eq_two.1 hc
    obtain ⟨C, a, hCa⟩ := separate hcc
    have := hdot _ (Phi_mem_ker (globally_affine_mem D C a))
    rw [hc2, Finset.sum_pair hcc] at this
    apply hCa
    generalize Phi (fun x => C + a x) c = p at this
    generalize Phi (fun x => C + a x) c' = p' at this
    revert p p'; decide

end AbelianCayleyHDX.Sec3

open AbelianCayleyHDX AbelianCayleyHDX.Sec3 in
theorem solution (h : ℕ) (hq : 8 ≤ 2 ^ h) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (hF : Fintype.card F = (2 ^ h) ^ 2) {t : ℕ} (ht : 1 ≤ t) (D : Finset (PG t F))
    (hD : IsSpanning D) :
    (∀ u v : (Fin t → F) → F, Phi (u + v) = Phi u + Phi v) ∧
    (∀ u ∈ affineSpace D, Phi u ∈ kerF2 (HD D)) ∧
    (∀ u ∈ affineSpace D, Phi u = 0 → u = 0) ∧
    2 * h * Module.finrank F (affineSpace D) ≤ Module.finrank (ZMod 2) (kerF2 (HD D)) ∧
    (∀ c c' : Omega F t, c ≠ c' → ∃ (C : F) (a : Module.Dual F (Fin t → F)),
      Phi (fun x => C + a x) c ≠ Phi (fun x => C + a x) c') ∧
    (∀ c : Omega F t, ∃ (C : F) (a : Module.Dual F (Fin t → F)), Phi (fun x => C + a x) c ≠ 0) ∧
    MinDistAtLeast3 (rowspan (HD D)) := by
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · norm_num at hq
    · exact hpos
  have : CharP F 2 := charP_two_of_card h hh hF
  refine ⟨Phi_add', fun u hu => Phi_mem_ker hu, fun u _ h => Phi_eq_zero h, ?_,
    fun c c' h => separate h, nonzero_at, minDist D⟩
  -- dimension count
  classical
  let f : affineSpace D → kerF2 (HD D) := fun u => ⟨Phi u.1, Phi_mem_ker u.2⟩
  have hf : Function.Injective f := by
    intro u v huv
    have : Phi u.1 = Phi v.1 := congrArg Subtype.val huv
    have h0 : Phi (u.1 - v.1) = 0 := by rw [Phi_sub', this, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (Phi_eq_zero h0))
  have hcard := Nat.card_le_card_of_injective f hf
  have e1 : Nat.card (affineSpace D) = Nat.card F ^ Module.finrank F (affineSpace D) :=
    Module.natCard_eq_pow_finrank
  have e2 : Nat.card (kerF2 (HD D)) =
      Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (kerF2 (HD D)) :=
    Module.natCard_eq_pow_finrank
  rw [e1, e2, Nat.card_eq_fintype_card (α := F), hF, Nat.card_zmod, ← pow_mul, ← pow_mul] at hcard
  have := (Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)).1 hcard
  calc 2 * h * Module.finrank F (affineSpace D)
      = h * (2 * Module.finrank F (affineSpace D)) := by ring
    _ ≤ _ := this
