-- Prove2me | solution 1 for AKSSorting.Core.chainW_exists
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-20T06:39:01.809908+00:00
-- url     : https://prove2.me/submissions/2c7d1670-b554-4105-90e0-af36fa3182c2

import Mathlib
import Definitions.Def_AKSSorting_Core_IsChain
import Definitions.Def_AKSSorting_Core_splitV

open AKSSorting.Core

/-- leaf `u` (value) is used by level `k` in the splitting -/
def splitP (i j k u : ℕ) : Prop :=
  j ≤ k ∧ k < i ∧ (u % 2 ^ (i - k) = 2 ^ (i - k - 1) ∨ (k = j ∧ u % 2 ^ (i - k) = 0))

lemma splitP_unique {i j k k' u : ℕ} (h : splitP i j k u) (h' : splitP i j k' u) : k = k' := by
  by_contra hne
  wlog hlt : k < k' generalizing k k'
  · exact this h' h (Ne.symm hne) (by omega)
  obtain ⟨hj, hi, hc⟩ := h
  obtain ⟨hj', hi', hc'⟩ := h'
  have hdvd : 2 ^ (i - k') ∣ 2 ^ (i - k) := Nat.pow_dvd_pow 2 (by omega)
  have hmod : u % 2 ^ (i - k') = (u % 2 ^ (i - k)) % 2 ^ (i - k') :=
    (Nat.mod_mod_of_dvd u hdvd).symm
  have hz : u % 2 ^ (i - k') = 0 := by
    rcases hc with hc | ⟨_, hc⟩
    · rw [hmod, hc]
      exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
    · rw [hmod, hc, Nat.zero_mod]
  rcases hc' with hc' | ⟨hk', _⟩
  · rw [hz] at hc'
    exact absurd hc'.symm (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  · omega

lemma splitP_aux (u : ℕ) : ∀ n, 1 ≤ n → u % 2 ^ n = 0 ∨ ∃ m < n, u % 2 ^ (m + 1) = 2 ^ m := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rcases Nat.mod_two_eq_zero_or_one u with h | h
    · left; simpa using h
    · right; exact ⟨0, by omega, by simpa using h⟩
  | succ n hn ih =>
    rcases ih with h | ⟨m, hm, h⟩
    · have hdvd : 2 ^ n ∣ 2 ^ (n + 1) := Nat.pow_dvd_pow 2 (by omega)
      have h1 : (u % 2 ^ (n + 1)) % 2 ^ n = 0 := by rw [Nat.mod_mod_of_dvd u hdvd, h]
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h1
      have hlt : u % 2 ^ (n + 1) < 2 ^ (n + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
      rw [hq, pow_succ] at hlt
      have hq2 : q < 2 := Nat.lt_of_mul_lt_mul_left hlt
      interval_cases q
      · left; simpa using hq
      · right; exact ⟨n, by omega, by simpa using hq⟩
    · right; exact ⟨m, by omega, h⟩

lemma splitP_exists {i j u : ℕ} (hj : j < i) : ∃ k, splitP i j k u := by
  rcases splitP_aux u (i - j) (by omega) with h | ⟨m, hm, h⟩
  · exact ⟨j, le_refl _, hj, Or.inr ⟨rfl, h⟩⟩
  · refine ⟨i - 1 - m, by omega, by omega, Or.inl ?_⟩
    have e1 : i - (i - 1 - m) = m + 1 := by omega
    rw [e1]; simpa using h
section
variable {R : Type} [LinearOrder R]

lemma firstElem_sub' (s : Finset R) : firstElem s ⊆ s := by
  unfold firstElem; split_ifs with h
  · simpa using Finset.min'_mem s h
  · simp

lemma firstElem_card' {s : Finset R} (h : s.Nonempty) : (firstElem s).card = 1 := by
  unfold firstElem; simp [h]

lemma mem_splitVLow_iff {i j k : ℕ} (C : Fin (2 ^ i) → Finset R) (hk : k < i)
    (t : Fin (2 ^ k)) (x : R) :
    x ∈ splitVLow C j k t ↔ ∃ u : Fin (2 ^ i), splitP i j k u.val ∧
      u.val / 2 ^ (i - k) = t.val ∧ x ∈ firstElem (C u) := by
  have hp : 0 < 2 ^ (i - k) := Nat.two_pow_pos _
  have hpp : 2 ^ (i - k) = 2 * 2 ^ (i - k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hz_mod : (zeroExt hk.le t).val % 2 ^ (i - k) = 0 := by
    simp [zeroExt]
  have hz_div : (zeroExt hk.le t).val / 2 ^ (i - k) = t.val := by
    simp [zeroExt, Nat.mul_div_cancel _ hp]
  have ho_mod : (oneZeroExt hk t).val % 2 ^ (i - k) = 2 ^ (i - k - 1) := by
    simp only [oneZeroExt]
    rw [Nat.mul_add_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  have ho_div : (oneZeroExt hk t).val / 2 ^ (i - k) = t.val := by
    simp only [oneZeroExt]
    rw [mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt (by omega), add_zero]
  unfold splitVLow
  rw [dif_pos hk]
  constructor
  · intro hx
    split_ifs at hx with h1 h2
    · simp at hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact ⟨_, ⟨by omega, hk, Or.inr ⟨h2, hz_mod⟩⟩, hz_div, hx⟩
      · exact ⟨_, ⟨by omega, hk, Or.inl ho_mod⟩, ho_div, hx⟩
    · exact ⟨_, ⟨by omega, hk, Or.inl ho_mod⟩, ho_div, hx⟩
  · rintro ⟨u, ⟨hjk, -, hc⟩, hut, hx⟩
    have hdm := Nat.div_add_mod u.val (2 ^ (i - k))
    rw [hut] at hdm
    rw [if_neg (by omega)]
    rcases hc with hc | ⟨hkj, hc⟩
    · have hu : u = oneZeroExt hk t := by
        ext; simp only [oneZeroExt]; rw [hc] at hdm; rw [← hdm, mul_comm]
      subst hu
      split_ifs
      · exact Finset.mem_union_right _ hx
      · exact hx
    · have hu : u = zeroExt hk.le t := by
        ext; simp only [zeroExt]; rw [hc] at hdm; rw [← hdm, mul_comm, add_zero]
      subst hu
      rw [if_pos hkj]
      exact Finset.mem_union_left _ hx

lemma splitV_low_eq {i j k : ℕ} (C : Fin (2 ^ i) → Finset R) (hk : k < i) :
    splitV C j k = splitVLow C j k := by
  funext t; unfold splitV; rw [if_pos hk]

lemma card_splitVLow {i j k : ℕ} (C : Fin (2 ^ i) → Finset R) (hk : k < i)
    (hne : ∀ u, (C u).Nonempty) (hdisj : ∀ x y, x ≠ y → Disjoint (C x) (C y))
    (t : Fin (2 ^ k)) :
    (splitVLow C j k t).card = if k < j then 0 else if k = j then 2 else 1 := by
  unfold splitVLow
  rw [dif_pos hk]
  split_ifs with h1 h2
  · simp
  · have hne' : zeroExt hk.le t ≠ oneZeroExt hk t := by
      intro h
      have := congrArg Fin.val h
      simp only [zeroExt, oneZeroExt] at this
      have : 0 < 2 ^ (i - k - 1) := Nat.two_pow_pos _
      omega
    rw [Finset.card_union_of_disjoint, firstElem_card' (hne _), firstElem_card' (hne _)]
    exact Finset.disjoint_of_subset_left (firstElem_sub' _)
      (Finset.disjoint_of_subset_right (firstElem_sub' _) (hdisj _ _ hne'))
  · exact firstElem_card' (hne _)
end

theorem splitV_spec' {R : Type} [LinearOrder R] {i j : ℕ} (C : Fin (2 ^ i) → Finset R)
    (hC : IsChain C) (hj : j < i) (hN : 2 ≤ chainN C) :
    (∀ k ≤ i, IsChain (splitV C j k)) ∧
    (∀ k ≤ i, ∀ k' ≤ i, k ≠ k' →
      Disjoint (chainUnion (splitV C j k)) (chainUnion (splitV C j k'))) ∧
    ((∀ k, j < k → k < i → chainN (splitV C j k) = 1) ∧
      chainN (splitV C j j) = 2 ∧
      (∀ k, k < j → chainN (splitV C j k) = 0)) ∧
    (∀ k, j ≤ k → k ≤ i → ∀ t' : Fin (2 ^ k), splitV C j k t' ⊆ subtreeUnion C k t') ∧
    (∀ t : Fin (2 ^ i),
      (C t ∩ (Finset.range i).biUnion fun k => chainUnion (splitV C j k)).card = 1) := by
  obtain ⟨hdisj, hcard⟩ := hC
  have hcardN : ∀ u, (C u).card = chainN C := fun u => hcard u _
  have hne : ∀ u, (C u).Nonempty := fun u => by
    rw [← Finset.card_pos, hcardN]; omega
  have huniq : ∀ (x : R) (u u' : Fin (2 ^ i)), x ∈ C u → x ∈ C u' → u = u' := by
    intro x u u' hx hx'
    by_contra h
    exact Finset.disjoint_left.mp (hdisj u u' h) hx hx'
  have mem_low : ∀ k, k < i → ∀ x, x ∈ chainUnion (splitVLow C j k) ↔
      ∃ u : Fin (2 ^ i), splitP i j k u.val ∧ x ∈ firstElem (C u) := by
    intro k hk x
    simp only [chainUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨u, hu, -, hx⟩ := (mem_splitVLow_iff C hk t x).mp ht
      exact ⟨u, hu, hx⟩
    · rintro ⟨u, hu, hx⟩
      have hlt : u.val / 2 ^ (i - k) < 2 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_sub_cancel' hk.le]
        exact u.isLt
      exact ⟨⟨_, hlt⟩, (mem_splitVLow_iff C hk _ x).mpr ⟨u, hu, rfl, hx⟩⟩
  set W := (Finset.Ico j i).biUnion fun k' => chainUnion (splitVLow C j k') with hW
  have mem_W : ∀ x, x ∈ W ↔ ∃ (u : Fin (2 ^ i)) (k : ℕ), splitP i j k u.val ∧ x ∈ firstElem (C u) := by
    intro x
    rw [hW, Finset.mem_biUnion]
    constructor
    · rintro ⟨k, hk, hx⟩
      obtain ⟨u, hu, hx⟩ := (mem_low k (Finset.mem_Ico.mp hk).2 x).mp hx
      exact ⟨u, k, hu, hx⟩
    · rintro ⟨u, k, hu, hx⟩
      exact ⟨k, Finset.mem_Ico.mpr ⟨hu.1, hu.2.1⟩, (mem_low k hu.2.1 x).mpr ⟨u, hu, hx⟩⟩
  have key : ∀ (t : Fin (2 ^ i)) x, x ∈ C t → (x ∈ W ↔ x ∈ firstElem (C t)) := by
    intro t x hxt
    rw [mem_W]
    constructor
    · rintro ⟨u, k, -, hx⟩
      rwa [huniq x u t (firstElem_sub' _ hx) hxt] at hx
    · intro hx
      obtain ⟨k, hk⟩ := splitP_exists (u := t.val) hj
      exact ⟨t, k, hk, hx⟩
  have top : ∀ t : Fin (2 ^ i), splitV C j i t = C t \ W := by
    intro t; unfold splitV; simp [hW]
  have top_eq : ∀ t : Fin (2 ^ i), C t \ W = C t \ firstElem (C t) := by
    intro t; ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ((key t x h1).mpr h)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ((key t x h1).mp h)⟩
  have hp_div : ∀ (k : ℕ) (hk : k < i) (t : Fin (2 ^ k)) x, x ∈ splitVLow C j k t →
      ∃ u : Fin (2 ^ i), u.val / 2 ^ (i - k) = t.val ∧ x ∈ C u := by
    intro k hk t x hx
    obtain ⟨u, -, hut, hx⟩ := (mem_splitVLow_iff C hk t x).mp hx
    exact ⟨u, hut, firstElem_sub' _ hx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases lt_or_eq_of_le hk with hk | rfl
    · rw [splitV_low_eq C hk]
      refine ⟨?_, ?_⟩
      · intro t1 t2 h12
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨u1, h1, hx1⟩ := hp_div k hk t1 x hx1
        obtain ⟨u2, h2, hx2⟩ := hp_div k hk t2 x hx2
        have := huniq x u1 u2 hx1 hx2
        subst this
        exact h12 (Fin.ext (h1.symm.trans h2))
      · intro t1 t2
        rw [card_splitVLow C hk hne hdisj, card_splitVLow C hk hne hdisj]
    · refine ⟨?_, ?_⟩
      · intro t1 t2 h12
        rw [top, top]
        exact Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset (hdisj t1 t2 h12))
      · intro t1 t2
        rw [top, top, top_eq, top_eq, Finset.card_sdiff_of_subset (firstElem_sub' _),
          Finset.card_sdiff_of_subset (firstElem_sub' _), firstElem_card' (hne _),
          firstElem_card' (hne _), hcardN, hcardN]
  · have mem_split : ∀ k, k < i → ∀ x, x ∈ chainUnion (splitV C j k) → x ∈ W := by
      intro k hk x hx
      rw [splitV_low_eq C hk] at hx
      obtain ⟨u, hu, hx⟩ := (mem_low k hk x).mp hx
      exact (mem_W x).mpr ⟨u, k, hu, hx⟩
    have mem_top : ∀ x, x ∈ chainUnion (splitV C j i) → x ∉ W := by
      intro x hx
      simp only [chainUnion, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
      obtain ⟨t, ht⟩ := hx
      rw [top] at ht
      exact (Finset.mem_sdiff.mp ht).2
    intro k hk k' hk' hkk'
    rw [Finset.disjoint_left]
    intro x hx hx'
    rcases lt_or_eq_of_le hk with hk | rfl
    · rcases lt_or_eq_of_le hk' with hk' | rfl
      · rw [splitV_low_eq C hk] at hx
        rw [splitV_low_eq C hk'] at hx'
        obtain ⟨u, hu, hxu⟩ := (mem_low k hk x).mp hx
        obtain ⟨u', hu', hxu'⟩ := (mem_low k' hk' x).mp hx'
        have := huniq x u u' (firstElem_sub' _ hxu) (firstElem_sub' _ hxu')
        subst this
        exact hkk' (splitP_unique hu hu')
      · exact mem_top x hx' (mem_split k hk x hx)
    · rcases lt_or_eq_of_le hk' with hk' | rfl
      · exact mem_top x hx (mem_split k' hk' x hx')
      · exact hkk' rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro k h1 h2
      unfold chainN
      rw [splitV_low_eq C h2, card_splitVLow C h2 hne hdisj, if_neg (by omega), if_neg (by omega)]
    · unfold chainN
      rw [splitV_low_eq C hj, card_splitVLow C hj hne hdisj, if_neg (by omega), if_pos rfl]
    · intro k hk
      unfold chainN
      rw [splitV_low_eq C (by omega), card_splitVLow C (by omega) hne hdisj, if_pos hk]
  · intro k hjk hk t' x hx
    simp only [subtreeUnion, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_or_eq_of_le hk with hk | rfl
    · rw [splitV_low_eq C hk] at hx
      obtain ⟨u, hu, hx⟩ := hp_div k hk t' x hx
      exact ⟨u, hu, hx⟩
    · rw [top] at hx
      exact ⟨t', by simp, (Finset.mem_sdiff.mp hx).1⟩
  · intro t
    have : (C t ∩ (Finset.range i).biUnion fun k => chainUnion (splitV C j k)) = firstElem (C t) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_range]
      constructor
      · rintro ⟨hxt, k, hk, hx⟩
        rw [splitV_low_eq C hk] at hx
        obtain ⟨u, hu, hx⟩ := (mem_low k hk x).mp hx
        exact (key t x hxt).mp ((mem_W x).mpr ⟨u, k, hu, hx⟩)
      · intro hx
        have hxt := firstElem_sub' _ hx
        obtain ⟨k, hk⟩ := splitP_exists (u := t.val) hj
        refine ⟨hxt, k, hk.2.1, ?_⟩
        rw [splitV_low_eq C hk.2.1]
        exact (mem_low k hk.2.1 x).mpr ⟨t, hk, hx⟩
    rw [this, firstElem_card' (hne _)]

section
variable {R : Type} [LinearOrder R]

lemma splitV_sub_union {i j k : ℕ} (D : Fin (2 ^ i) → Finset R) (t : Fin (2 ^ k)) (x : R)
    (hx : x ∈ splitV D j k t) : ∃ u, x ∈ D u := by
  unfold splitV at hx
  split_ifs at hx with h1 h2
  · obtain ⟨u, -, -, hu⟩ := (mem_splitVLow_iff D h1 t x).mp hx
    exact ⟨u, firstElem_sub' _ hu⟩
  · exact ⟨_, (Finset.mem_sdiff.mp hx).1⟩
  · simp at hx

lemma chain_zero_empty {k : ℕ} (V : Fin (2 ^ k) → Finset R) (hV : IsChain V) (h0 : chainN V = 0)
    (t : Fin (2 ^ k)) : V t = ∅ := by
  rw [← Finset.card_eq_zero, hV.2 t ⟨0, Nat.two_pow_pos k⟩]; exact h0

def restW {i : ℕ} (C : Fin (2 ^ i) → Finset R) (W : (k : ℕ) → Fin (2 ^ k) → Finset R) :
    Fin (2 ^ i) → Finset R :=
  fun t => C t \ (Finset.range i).biUnion fun k => chainUnion (W k)

def GoodW {i : ℕ} (C : Fin (2 ^ i) → Finset R) (n : ℕ → ℕ) (W : (k : ℕ) → Fin (2 ^ k) → Finset R)
    (r : ℕ) : Prop :=
  (∀ k < i, IsChain (W k)) ∧
  (∀ k < i, ∀ k' < i, k ≠ k' → Disjoint (chainUnion (W k)) (chainUnion (W k'))) ∧
  (∀ k < i, ∀ t' : Fin (2 ^ k), W k t' ⊆ subtreeUnion C k t') ∧
  (∀ k < i, chainN (W k) = n k) ∧
  IsChain (restW C W) ∧ chainN (restW C W) + r = chainN C

def deltaW (j k : ℕ) : ℕ := if k = j then 2 else if j < k then 1 else 0

lemma goodW_step {i j : ℕ} (C : Fin (2 ^ i) → Finset R) (n : ℕ → ℕ)
    (W : (k : ℕ) → Fin (2 ^ k) → Finset R) (r : ℕ) (hg : GoodW C n W r) (hj : j < i)
    (hr : r + 2 ≤ chainN C) :
    ∃ W', GoodW C (fun k => n k + deltaW j k) W' (r + 1) := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hg
  set D := restW C W with hD
  have hND : 2 ≤ chainN D := by omega
  obtain ⟨s1, s2, ⟨s3a, s3b, s3c⟩, s4, s5⟩ := splitV_spec' D g5 hj hND
  set V := fun k => splitV D j k with hV
  have hDW : ∀ u x, x ∈ D u → ∀ k < i, x ∉ chainUnion (W k) := by
    intro u x hx k hk hxW
    simp only [hD, restW, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range] at hx
    exact hx.2 ⟨k, hk, hxW⟩
  have hVD : ∀ k x, x ∈ chainUnion (V k) → ∃ u, x ∈ D u := by
    intro k x hx
    simp only [chainUnion, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    obtain ⟨t, ht⟩ := hx
    exact splitV_sub_union D t x ht
  have hWV : ∀ k < i, ∀ k', Disjoint (chainUnion (W k)) (chainUnion (V k')) := by
    intro k hk k'
    rw [Finset.disjoint_left]
    intro x hxW hxV
    obtain ⟨u, hu⟩ := hVD k' x hxV
    exact hDW u x hu k hk hxW
  have hVsub : ∀ k t, V k t ⊆ chainUnion (V k) := fun k t =>
    Finset.subset_biUnion_of_mem (V k) (Finset.mem_univ t)
  have hWsub : ∀ k t, W k t ⊆ chainUnion (W k) := fun k t =>
    Finset.subset_biUnion_of_mem (W k) (Finset.mem_univ t)
  have hWVt : ∀ k < i, ∀ t t', Disjoint (W k t) (V k t') := fun k hk t t' =>
    Finset.disjoint_of_subset_left (hWsub k t)
      (Finset.disjoint_of_subset_right (hVsub k t') (hWV k hk k))
  have hVcard : ∀ k < i, chainN (V k) = deltaW j k := by
    intro k hk
    unfold deltaW
    split_ifs with h1 h2
    · subst h1; exact s3b
    · exact s3a k h2 hk
    · exact s3c k (by omega)
  have eU : ∀ m, chainUnion (fun t => W m t ∪ V m t) = chainUnion (W m) ∪ chainUnion (V m) := by
    intro m; ext x; simp [chainUnion, Finset.mem_biUnion, exists_or]
  have eRest : restW C (fun k t => W k t ∪ V k t) =
      fun t => D t \ (Finset.range i).biUnion fun k => chainUnion (V k) := by
    funext t; ext x
    simp only [restW, hD, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range, eU,
      Finset.mem_union]
    constructor
    · rintro ⟨hC, h⟩
      exact ⟨⟨hC, fun ⟨k, hk, hx⟩ => h ⟨k, hk, Or.inl hx⟩⟩, fun ⟨k, hk, hx⟩ => h ⟨k, hk, Or.inr hx⟩⟩
    · rintro ⟨⟨hC, h1⟩, h2⟩
      exact ⟨hC, fun ⟨k, hk, hx⟩ => hx.elim (fun hx => h1 ⟨k, hk, hx⟩) (fun hx => h2 ⟨k, hk, hx⟩)⟩
  have hcardU : ∀ t, (D t \ (Finset.range i).biUnion fun k => chainUnion (V k)).card + 1 =
      (D t).card := by
    intro t
    rw [← s5 t]
    exact Finset.card_sdiff_add_card_inter _ _
  refine ⟨fun k t => W k t ∪ V k t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    refine ⟨?_, ?_⟩
    · intro t t' htt'
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨(g1 k hk).1 t t' htt', hWVt k hk t t'⟩,
        ⟨(hWVt k hk t' t).symm, (s1 k hk.le).1 t t' htt'⟩⟩
    · intro t t'
      rw [Finset.card_union_of_disjoint (hWVt k hk t t), Finset.card_union_of_disjoint (hWVt k hk t' t'),
        (g1 k hk).2 t t', (s1 k hk.le).2 t t']
  · intro k hk k' hk' hkk'
    rw [eU, eU, Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨g2 k hk k' hk' hkk', hWV k hk k'⟩, ⟨(hWV k' hk' k).symm, s2 k hk.le k' hk'.le hkk'⟩⟩
  · intro k hk t'
    apply Finset.union_subset (g3 k hk t')
    by_cases hjk : j ≤ k
    · intro x hx
      have hx' := s4 k hjk hk.le t' hx
      simp only [subtreeUnion, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hx' ⊢
      obtain ⟨u, hu, hxu⟩ := hx'
      exact ⟨u, hu, (Finset.mem_sdiff.mp hxu).1⟩
    · rw [chain_zero_empty (V k) (s1 k hk.le) (s3c k (by omega)) t']
      exact Finset.empty_subset _
  · intro k hk
    show (W k _ ∪ V k _).card = _
    rw [Finset.card_union_of_disjoint (hWVt k hk _ _)]
    show chainN (W k) + chainN (V k) = _
    rw [g4 k hk, hVcard k hk]
  · rw [eRest]
    refine ⟨fun t t' htt' => Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset (g5.1 t t' htt')), fun t t' => ?_⟩
    have h1 := hcardU t; have h2 := hcardU t'
    rw [g5.2 t t'] at h1; dsimp only; omega
  · rw [eRest]
    have h1 := hcardU ⟨0, Nat.two_pow_pos i⟩
    have h3 : chainN D = (D ⟨0, Nat.two_pow_pos i⟩).card := rfl
    show (D ⟨0, Nat.two_pow_pos i⟩ \ _).card + (r + 1) = chainN C
    omega

lemma goodW_iter {i j : ℕ} (C : Fin (2 ^ i) → Finset R) (n : ℕ → ℕ)
    (W : (k : ℕ) → Fin (2 ^ k) → Finset R) (r : ℕ) (hg : GoodW C n W r) (hj : j < i) :
    ∀ m, (m = 0 ∨ r + m + 1 < chainN C) →
      ∃ W', GoodW C (fun k => n k + m * deltaW j k) W' (r + m) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨W, by simpa using hg⟩
  | succ m ih =>
    intro hm
    obtain ⟨W1, h1⟩ := ih (by omega)
    obtain ⟨W2, h2⟩ := goodW_step C _ W1 (r + m) h1 hj (by omega)
    refine ⟨W2, ?_⟩
    have e : (fun k => n k + (m + 1) * deltaW j k) = fun k => (n k + m * deltaW j k) + deltaW j k := by
      funext k; ring
    rw [e, show r + (m + 1) = r + m + 1 by ring]
    exact h2

lemma chainW_core {i : ℕ} (C : Fin (2 ^ i) → Finset R)
    (hC : IsChain C) (a : ℕ → ℕ)
    (h2a : 2 * ∑ k ∈ Finset.range i, a k < chainN C)
    (h2b : ∀ s < i, (∃ s' < s, 0 < a s') → ∑ k ∈ Finset.range s, a k < a s) :
    ∀ s ≤ i, ∃ (n : ℕ → ℕ) (W : (k : ℕ) → Fin (2 ^ k) → Finset R) (r : ℕ), GoodW C n W r ∧
      (∀ k < s, a k ≤ n k + 1 ∧ n k ≤ a k) ∧ (∀ k, s ≤ k → k < i → n k = r) ∧
      2 * r ≤ ∑ k ∈ Finset.range s, a k := by
  intro s
  induction s with
  | zero =>
    intro _
    refine ⟨fun _ => 0, fun _ _ => ∅, 0, ?_, by simp, by simp, by simp⟩
    have hE : ∀ k, chainUnion (fun _ : Fin (2 ^ k) => (∅ : Finset R)) = ∅ := fun k => by
      ext; simp [chainUnion]
    have hE' : ((Finset.range i).biUnion fun k => chainUnion (fun _ : Fin (2 ^ k) => (∅ : Finset R))) = ∅ := by
      ext x; simp [hE]
    have e : restW C (fun _ _ => ∅) = C := by
      funext t; simp only [restW]; rw [hE', Finset.sdiff_empty]
    refine ⟨fun k _ => ⟨fun _ _ _ => by simp, fun _ _ => by simp⟩, fun _ _ _ _ _ => by simp [hE],
      fun _ _ _ => by simp, fun _ _ => by simp [chainN], ?_, ?_⟩
    · rw [e]; exact hC
    · rw [e]; rfl
  | succ s ih =>
    intro hs
    obtain ⟨n, W, r, hg, hb, hl, hr⟩ := ih (by omega)
    have hsi : s < i := by omega
    have hsum : ∑ k ∈ Finset.range (s + 1), a k ≤ ∑ k ∈ Finset.range i, a k :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hs)
    have hrs : r ≤ a s := by
      by_cases hex : ∃ s' < s, 0 < a s'
      · have := h2b s hsi hex; omega
      · push Not at hex
        have : ∑ k ∈ Finset.range s, a k = 0 :=
          Finset.sum_eq_zero fun k hk => by have := hex k (Finset.mem_range.mp hk); omega
        omega
    rw [Finset.sum_range_succ] at hsum
    set m := (a s - r) / 2 with hm
    obtain ⟨W', hg'⟩ := goodW_iter C n W r hg hsi m (by omega)
    refine ⟨_, W', r + m, hg', ?_, ?_, ?_⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · have hd : deltaW s k = 0 := by unfold deltaW; rw [if_neg (by omega), if_neg (by omega)]
        simp only [hd, mul_zero, add_zero]; exact hb k hk
      · have hd : deltaW k k = 2 := by simp [deltaW]
        simp only [hd]; rw [hl k le_rfl hsi]; omega
    · intro k hk1 hk2
      have hd : deltaW s k = 1 := by unfold deltaW; rw [if_neg (by omega), if_pos (by omega)]
      simp only [hd, mul_one]; rw [hl k (by omega) hk2]
    · rw [Finset.sum_range_succ]; omega
end

theorem solution {R : Type} [DecidableEq R] {i : ℕ} (C : Fin (2 ^ i) → Finset R)
    (hC : IsChain C) (a : ℕ → ℕ)
    (h2a : 2 * ∑ k ∈ Finset.range i, a k < chainN C)
    (h2b : ∀ s < i, (∃ s' < s, 0 < a s') → ∑ k ∈ Finset.range s, a k < a s) :
    ∃ W : (k : ℕ) → Fin (2 ^ k) → Finset R,
      (∀ k < i, IsChain (W k)) ∧
      (∀ k < i, ∀ k' < i, k ≠ k' → Disjoint (chainUnion (W k)) (chainUnion (W k'))) ∧
      (∀ k < i, ∀ t' : Fin (2 ^ k), W k t' ⊆ subtreeUnion C k t') ∧
      (∀ k < i, (a k : ℤ) - 1 ≤ (chainN (W k) : ℤ) ∧ chainN (W k) ≤ a k) ∧
      (IsChain (fun t => C t \ (Finset.range i).biUnion fun k => chainUnion (W k)) ∧
        (chainN C : ℤ) - ∑ k ∈ Finset.range i, (a k : ℤ) ≤
          (chainN (fun t => C t \ (Finset.range i).biUnion fun k => chainUnion (W k)) : ℤ) ∧
        chainN (fun t => C t \ (Finset.range i).biUnion fun k => chainUnion (W k)) ≤
          chainN C) := by
  let L : LinearOrder R := IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨n, W, r, ⟨g1, g2, g3, g4, g5, g6⟩, hb, -, hr⟩ :=
    chainW_core (R := R) C (by convert hC) a (by convert h2a) (by convert h2b) i le_rfl
  unfold restW at g5 g6
  have g6' : chainN (fun t => C t \ (Finset.range i).biUnion fun k => chainUnion (W k)) + r =
      chainN C := by convert g6
  refine ⟨W, fun k hk => by convert g1 k hk, fun k hk k' hk' h => by convert g2 k hk k' hk' h,
    fun k hk t' => by convert g3 k hk t', fun k hk => ?_, by convert g5, ?_, ?_⟩
  · have := hb k hk; have h4 := g4 k hk
    have h4' : chainN (W k) = n k := by convert h4
    rw [h4']; omega
  · have : ((∑ k ∈ Finset.range i, a k : ℕ) : ℤ) = ∑ k ∈ Finset.range i, (a k : ℤ) := by push_cast; rfl
    rw [← this]
    omega
  · omega
