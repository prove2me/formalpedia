-- Prove2me | solution 1 for AppliedComb.ManyFaces.covers_structure
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:03:33.473973+00:00
-- url     : https://prove2.me/submissions/80ffb3c5-3df0-440f-bac7-44b3aa85fe8b

import Mathlib
import Definitions.Def_AppliedComb_ManyFaces_partitionDominance

open Finset
open AppliedComb.ManyFaces

namespace CovAux

lemma entry_succ (L : List ℕ) (x : ℕ) : entry L (x + 1) = L.getD x 0 := by
  simp [entry]

lemma entry_zero (L : List ℕ) : entry L 0 = 0 := by simp [entry]

lemma entry_of_length_lt (L : List ℕ) {k : ℕ} (hk : L.length < k) : entry L k = 0 := by
  obtain ⟨x, rfl⟩ : ∃ x, k = x + 1 := ⟨k - 1, by omega⟩
  rw [entry_succ]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ x)]

lemma entry_pos {t : ℕ} {L : List ℕ} (hL : IsPartition t L) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ L.length) : 0 < entry L k := by
  obtain ⟨x, rfl⟩ : ∃ x, k = x + 1 := ⟨k - 1, by omega⟩
  rw [entry_succ]
  have : x < L.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this, Option.getD_some]
  exact hL.2.1 _ (List.getElem_mem this)

lemma entry_anti {t : ℕ} {L : List ℕ} (hL : IsPartition t L) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    entry L b ≤ entry L a := by
  by_cases hb : b ≤ L.length
  · obtain ⟨x, rfl⟩ : ∃ x, a = x + 1 := ⟨a - 1, by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, b = y + 1 := ⟨b - 1, by omega⟩
    rw [entry_succ, entry_succ]
    rcases (show x ≤ y by omega).eq_or_lt with rfl | hlt
    · exact le_rfl
    · have := List.pairwise_iff_getElem.mp hL.1 x y (by omega) (by omega) hlt
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x < L.length by omega),
        List.getElem?_eq_getElem (show y < L.length by omega)] using this
  · rw [entry_of_length_lt L (by omega)]; exact Nat.zero_le _

lemma ps_eq (L : List ℕ) (j : ℕ) : (L.take j).sum = ∑ x ∈ range j, entry L (x + 1) := by
  have : ∀ j, (L.take j).sum = ∑ x ∈ range j, L.getD x 0 := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ← ih]
      by_cases hk : k < L.length
      · rw [List.sum_take_succ L k hk]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      · have h1 : L.length ≤ k := not_lt.mp hk
        rw [List.take_of_length_le h1, List.take_of_length_le (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]
  rw [this j]
  exact sum_congr rfl fun x _ => (entry_succ L x).symm

lemma list_ext_entries {t : ℕ} {L L' : List ℕ} (hL : IsPartition t L) (hL' : IsPartition t L')
    (h : ∀ k, 1 ≤ k → entry L k = entry L' k) : L = L' := by
  have hlen : L.length = L'.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := h (L.length + 1) (by omega)
      rw [entry_of_length_lt L (by omega)] at h1
      have := entry_pos hL' (by omega) (by omega : L.length + 1 ≤ L'.length)
      omega
    · have h1 := h (L'.length + 1) (by omega)
      rw [entry_of_length_lt L' (by omega)] at h1
      have := entry_pos hL (by omega) (by omega : L'.length + 1 ≤ L.length)
      omega
  refine List.ext_getElem hlen fun x h1 h2 => ?_
  have := h (x + 1) (by omega)
  rw [entry_succ, entry_succ] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] using this


lemma sum_map_range (f : ℕ → ℕ) : ∀ N : ℕ, ((List.range N).map f).sum = ∑ j ∈ range N, f j := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The partition string `(u 1, …, u ℓ)`. -/
def mk (u : ℕ → ℕ) (ℓ : ℕ) : List ℕ := (List.range ℓ).map (fun x => u (x + 1))

lemma mk_length (u : ℕ → ℕ) (ℓ : ℕ) : (mk u ℓ).length = ℓ := by simp [mk]

lemma entry_mk (u : ℕ → ℕ) (ℓ : ℕ) (hu : ∀ k, ℓ < k → u k = 0) {k : ℕ} (hk : 1 ≤ k) :
    entry (mk u ℓ) k = u k := by
  obtain ⟨x, rfl⟩ : ∃ x, k = x + 1 := ⟨k - 1, by omega⟩
  rw [entry_succ]
  by_cases hx : x < ℓ
  · simp [mk, List.getD_eq_getElem?_getD, hx]
  · have h1 : (mk u ℓ).length ≤ x := by rw [mk_length]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, hu (x + 1) (by omega)]

lemma anti_of_succ {u : ℕ → ℕ} (h : ∀ k, 1 ≤ k → u (k + 1) ≤ u k) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b) : u b ≤ u a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (h b (by omega)).trans ih

lemma isPartition_mk {t : ℕ} (u : ℕ → ℕ) (ℓ : ℕ) (hanti : ∀ k, 1 ≤ k → u (k + 1) ≤ u k)
    (hpos : ∀ k, 1 ≤ k → k ≤ ℓ → 0 < u k) (hsum : ∑ x ∈ range ℓ, u (x + 1) = t) :
    IsPartition t (mk u ℓ) := by
  refine ⟨?_, ?_, ?_⟩
  · refine List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_
    simp only [mk, List.getElem_map, List.getElem_range]
    exact anti_of_succ hanti (by omega) (by omega)
  · intro v hv
    simp only [mk, List.mem_map, List.mem_range] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact hpos (x + 1) (by omega) (by omega)
  · rw [mk, sum_map_range]; exact hsum


/-- Partial sums of a dominated pair. -/
lemma ps_le_of_dominates {t : ℕ} {V W : List ℕ} (hV : IsPartition t V) (hW : IsPartition t W)
    (hd : Dominates V W) (j : ℕ) : (W.take j).sum ≤ (V.take j).sum := by
  by_cases hj : j ≤ V.length
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · exact hd.2 j hj0 hj
  · rw [List.take_of_length_le (by omega : V.length ≤ j), hV.2.2]
    have := List.sum_take_add_sum_drop W j
    rw [hW.2.2] at this; omega

lemma sum_indicator (c : ℕ) (h1 : 1 ≤ c) :
    ∀ ℓ : ℕ, ∑ x ∈ range ℓ, (if x + 1 = c then 1 else 0) = if c ≤ ℓ then 1 else 0 := by
  intro ℓ
  induction ℓ with
  | zero => simp; omega
  | succ ℓ ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

/-- The first-difference / plateau / drop data of a covering pair. -/
lemma cov_data {t : ℕ} {V W : List ℕ} (hV : IsPartition t V) (hW : IsPartition t W)
    (hd : Dominates V W) (hne : V ≠ W) :
    ∃ i a b : ℕ, 1 ≤ i ∧ i ≤ a ∧ a < b ∧ a ≤ V.length ∧ b ≤ V.length + 1 ∧ 2 ≤ entry V i ∧
      (∀ k, 1 ≤ k → k < i → entry V k = entry W k) ∧
      (∀ x, i ≤ x → x ≤ a → entry V x = entry V i) ∧
      entry V (a + 1) < entry V i ∧
      (∀ x, a < x → x < b → entry V x = entry V i - 1) ∧
      entry V b + 2 ≤ entry V i ∧
      (∀ k, i ≤ k → k < b → (W.take k).sum + 1 ≤ (V.take k).sum) := by
  have hm : V.length ≤ W.length := hd.1
  have hex : ∃ k, 1 ≤ k ∧ entry V k ≠ entry W k := by
    by_contra hno
    push Not at hno
    exact hne (list_ext_entries hV hW hno)
  obtain ⟨i, hi1, hine, hbefore⟩ : ∃ i, 1 ≤ i ∧ entry V i ≠ entry W i ∧
      ∀ k, 1 ≤ k → k < i → entry V k = entry W k := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk hki => ?_⟩
    by_contra hh
    exact Nat.find_min hex hki ⟨hk, hh⟩
  -- prefix sums agree before i, and compare at i
  have hpre : (V.take (i - 1)).sum = (W.take (i - 1)).sum := by
    rw [ps_eq, ps_eq]
    refine sum_congr rfl fun x hx => hbefore (x + 1) (by omega) (by have := mem_range.mp hx; omega)
  have hVi : (V.take i).sum = (V.take (i - 1)).sum + entry V i := by
    rw [ps_eq, ps_eq]
    obtain ⟨y, rfl⟩ : ∃ y, i = y + 1 := ⟨i - 1, by omega⟩
    simp [sum_range_succ]
  have hWi : (W.take i).sum = (W.take (i - 1)).sum + entry W i := by
    rw [ps_eq, ps_eq]
    obtain ⟨y, rfl⟩ : ∃ y, i = y + 1 := ⟨i - 1, by omega⟩
    simp [sum_range_succ]
  have hle := ps_le_of_dominates hV hW hd i
  have hvw : entry W i < entry V i := by omega
  have him : i ≤ V.length := by
    by_contra h
    rw [entry_of_length_lt V (by omega)] at hvw; omega
  have hwpos : 0 < entry W i := entry_pos hW hi1 (by omega)
  have hv2 : 2 ≤ entry V i := by omega
  -- end of the plateau
  have hex1 : ∃ k, i < k ∧ entry V k < entry V i :=
    ⟨V.length + 1, by omega, by rw [entry_of_length_lt V (by omega)]; omega⟩
  obtain ⟨a, hia, hplat, hdrop⟩ : ∃ a, i ≤ a ∧ (∀ x, i ≤ x → x ≤ a → entry V x = entry V i) ∧
      entry V (a + 1) < entry V i := by
    refine ⟨Nat.find hex1 - 1, ?_, ?_, ?_⟩
    · have := (Nat.find_spec hex1).1; omega
    · intro x hx1 hx2
      rcases hx1.eq_or_lt with rfl | hlt
      · rfl
      · have hlt' : x < Nat.find hex1 := by omega
        have := Nat.find_min hex1 hlt'
        have h2 := entry_anti hV hi1 hx1
        push Not at this
        have := this hlt
        omega
    · have := (Nat.find_spec hex1).1
      have e : Nat.find hex1 - 1 + 1 = Nat.find hex1 := by omega
      rw [e]; exact (Nat.find_spec hex1).2
  have hamv : a ≤ V.length := by
    by_contra h
    have := hplat a hia le_rfl
    rw [entry_of_length_lt V (by omega)] at this; omega
  -- the target index
  have hex2 : ∃ k, a < k ∧ entry V k + 2 ≤ entry V i :=
    ⟨V.length + 1, by omega, by rw [entry_of_length_lt V (by omega)]; omega⟩
  obtain ⟨b, hab, hbm, hbv, hmid⟩ : ∃ b, a < b ∧ b ≤ V.length + 1 ∧ entry V b + 2 ≤ entry V i ∧
      (∀ x, a < x → x < b → entry V x = entry V i - 1) := by
    refine ⟨Nat.find hex2, (Nat.find_spec hex2).1, Nat.find_min' hex2 ⟨by omega, ?_⟩,
      (Nat.find_spec hex2).2, ?_⟩
    · rw [entry_of_length_lt V (by omega)]; omega
    · intro x hx1 hx2
      have h1 := Nat.find_min hex2 hx2
      push Not at h1
      have h2 := h1 hx1
      have h3 : entry V x ≤ entry V (a + 1) := entry_anti hV (by omega) (by omega)
      omega
  refine ⟨i, a, b, hi1, hia, hab, hamv, hbm, hv2, hbefore, hplat, hdrop, hmid, hbv, ?_⟩
  -- key inequality by induction
  intro k hik
  induction k, hik using Nat.le_induction with
  | base => intro _; omega
  | succ k hik ih =>
    intro hkb
    have ih' := ih (by omega)
    have e1 : (V.take (k + 1)).sum = (V.take k).sum + entry V (k + 1) := by
      rw [ps_eq, ps_eq]; simp [sum_range_succ]
    have e2 : (W.take (k + 1)).sum = (W.take k).sum + entry W (k + 1) := by
      rw [ps_eq, ps_eq]; simp [sum_range_succ]
    have hwk : entry W (k + 1) ≤ entry W i := entry_anti hW hi1 (by omega)
    have hvk : entry W i ≤ entry V (k + 1) := by
      by_cases hka : k + 1 ≤ a
      · have := hplat (k + 1) (by omega) hka; omega
      · have := hmid (k + 1) (by omega) hkb; omega
    omega


theorem covers_main {t : ℕ} {V W : List ℕ} (hV : IsPartition t V) (hW : IsPartition t W)
    (hcov : Covers t V W) :
    W.length ≤ V.length + 1 ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ W.length ∧
        (∀ α : ℕ, 1 ≤ α → α < i → entry V α = entry W α) ∧
        (∀ β : ℕ, j < β → β ≤ V.length → entry V β = entry W β) ∧
        entry V i = 1 + entry W i ∧
        ((j ≤ V.length ∧ entry W j = 1 + entry V j) ∨
          (j = W.length ∧ W.length = V.length + 1 ∧ entry W j = 1)) ∧
        (i + 1 < j → ∀ γ : ℕ, i < γ → γ < j →
          entry W γ = entry V γ ∧ entry V γ = entry V i - 1) := by
  obtain ⟨-, -, hd, hne, hmin⟩ := hcov
  obtain ⟨i, a, b, hi1, hia, hab, hamv, hbm, hv2, hbefore, hplat, hdrop, hmid, hbv, hkey⟩ :=
    cov_data hV hW hd hne
  have hm : V.length ≤ W.length := hd.1
  have hva : entry V a = entry V i := hplat a hia le_rfl
  have hv1 : 1 ≤ entry V a := by omega
  have hℓcases : ∃ ℓ : ℕ, (b = V.length + 1 ∧ ℓ = V.length + 1) ∨ (b ≤ V.length ∧ ℓ = V.length) := by
    by_cases hb : b = V.length + 1
    · exact ⟨V.length + 1, Or.inl ⟨hb, rfl⟩⟩
    · exact ⟨V.length, Or.inr ⟨by omega, rfl⟩⟩
  obtain ⟨ℓ, hℓ⟩ := hℓcases
  have hℓm : V.length ≤ ℓ := by omega
  have hbℓ : b ≤ ℓ := by omega
  have haℓ : a ≤ ℓ := by omega
  obtain ⟨u, hu_a, hu_b, hu_other⟩ : ∃ u : ℕ → ℕ, u a = entry V a - 1 ∧ u b = entry V b + 1 ∧
      ∀ k, k ≠ a → k ≠ b → u k = entry V k := by
    refine ⟨fun k => if k = a then entry V k - 1 else if k = b then entry V k + 1 else entry V k,
      ?_, ?_, ?_⟩
    · simp
    · have : b ≠ a := by omega
      simp [this]
    · intro k h1 h2; simp [h1, h2]
  have hu_zero : ∀ k, ℓ < k → u k = 0 := by
    intro k hk
    rw [hu_other k (by omega) (by omega)]
    exact entry_of_length_lt V (by omega)
  have hu_anti : ∀ k, 1 ≤ k → u (k + 1) ≤ u k := by
    intro k hk
    have hvs : entry V (k + 1) ≤ entry V k := entry_anti hV hk (by omega)
    by_cases h1 : k = a
    · subst h1
      by_cases h : k + 1 = b
      · rw [h, hu_b, hu_a]; omega
      · rw [hu_other (k + 1) (by omega) h, hu_a]; omega
    · by_cases h2 : k + 1 = a
      · rw [h2, hu_a, hu_other k h1 (by omega)]; rw [h2] at hvs; omega
      · by_cases h3 : k = b
        · subst h3
          rw [hu_other (k + 1) (by omega) (by omega), hu_b]; omega
        · by_cases h4 : k + 1 = b
          · rw [h4, hu_b, hu_other k h1 h3]
            have := hmid k (by omega) (by omega)
            omega
          · rw [hu_other (k + 1) h2 h4, hu_other k h1 h3]; exact hvs
  have hu_pos : ∀ k, 1 ≤ k → k ≤ ℓ → 0 < u k := by
    intro k hk1 hkℓ
    by_cases h1 : k = a
    · subst h1; rw [hu_a]; omega
    · by_cases h2 : k = b
      · subst h2; rw [hu_b]; omega
      · rw [hu_other k h1 h2]
        exact entry_pos hV hk1 (by omega)
  have hind : ∀ j, ∑ x ∈ range j, u (x + 1) + (if a ≤ j then 1 else 0) =
      ∑ x ∈ range j, entry V (x + 1) + (if b ≤ j then 1 else 0) := by
    intro j
    have hpt : ∀ x, u (x + 1) + (if x + 1 = a then 1 else 0) =
        entry V (x + 1) + (if x + 1 = b then 1 else 0) := by
      intro x
      by_cases h1 : x + 1 = a
      · rw [if_pos h1, if_neg (by omega), h1, hu_a]; omega
      · by_cases h2 : x + 1 = b
        · rw [if_neg h1, if_pos h2, h2, hu_b]
        · rw [if_neg h1, if_neg h2, hu_other _ h1 h2]
    have h1 : ∑ x ∈ range j, (u (x + 1) + (if x + 1 = a then 1 else 0)) =
        ∑ x ∈ range j, (entry V (x + 1) + (if x + 1 = b then 1 else 0)) :=
      sum_congr rfl fun x _ => hpt x
    rw [sum_add_distrib, sum_add_distrib, sum_indicator a (by omega), sum_indicator b (by omega)] at h1
    exact h1
  have hsum : ∑ x ∈ range ℓ, u (x + 1) = t := by
    have h1 := hind ℓ
    rw [if_pos haℓ, if_pos hbℓ] at h1
    have h2 : ∑ x ∈ range ℓ, entry V (x + 1) = t := by
      rw [← ps_eq, List.take_of_length_le hℓm]; exact hV.2.2
    omega
  -- the intermediate partition
  have hUp : IsPartition t (mk u ℓ) := isPartition_mk u ℓ hu_anti hu_pos hsum
  have hentU : ∀ k, 1 ≤ k → entry (mk u ℓ) k = u k := fun k hk => entry_mk u ℓ hu_zero hk
  have hpsU : ∀ j, ((mk u ℓ).take j).sum = ∑ x ∈ range j, u (x + 1) := by
    intro j
    rw [ps_eq]
    exact sum_congr rfl fun x _ => hentU (x + 1) (by omega)
  have hpsV : ∀ j, (V.take j).sum = ∑ x ∈ range j, entry V (x + 1) := fun j => ps_eq V j
  have hdVU : Dominates V (mk u ℓ) := by
    refine ⟨by rw [mk_length]; exact hℓm, fun j _ _ => ?_⟩
    rw [hpsU, hpsV]
    have := hind j
    split_ifs at this <;> omega
  have hdUW : Dominates (mk u ℓ) W := by
    have hℓn : ℓ ≤ W.length := by
      rcases hℓ with ⟨hb, hℓe⟩ | ⟨hb, hℓe⟩
      · by_contra hlt
        have hn : W.length = V.length := by omega
        have hk := hkey V.length (by omega) (by omega)
        rw [List.take_of_length_le (by omega : W.length ≤ V.length), hW.2.2,
          List.take_of_length_le (le_refl _), hV.2.2] at hk
        omega
      · omega
    refine ⟨by rw [mk_length]; exact hℓn, fun j _ _ => ?_⟩
    rw [hpsU]
    have hPV : (W.take j).sum ≤ (V.take j).sum := ps_le_of_dominates hV hW hd j
    rw [hpsV] at hPV
    have := hind j
    by_cases hja : a ≤ j
    · by_cases hjb : b ≤ j
      · rw [if_pos hja, if_pos hjb] at this; omega
      · have hk := hkey j (by omega) (by omega)
        rw [hpsV] at hk
        rw [if_pos hja, if_neg hjb] at this
        omega
    · have hjb : ¬ b ≤ j := by omega
      rw [if_neg hja, if_neg hjb] at this
      omega
  have hUV : mk u ℓ ≠ V := by
    intro h
    have h1 := hentU a (by omega)
    rw [h, hu_a] at h1
    omega
  have hUW : mk u ℓ = W := (hmin _ hUp hdVU hdUW).resolve_left hUV
  have hwe : ∀ k, 1 ≤ k → entry W k = u k := by
    intro k hk; rw [← hUW]; exact hentU k hk
  have hWl : W.length = ℓ := by rw [← hUW, mk_length]
  refine ⟨by omega, a, b, by omega, hab, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro α h1 h2
    rw [hwe α h1, hu_other α (by omega) (by omega)]
  · intro β h1 h2
    rw [hwe β (by omega), hu_other β (by omega) (by omega)]
  · rw [hwe a (by omega), hu_a]; omega
  · rcases hℓ with ⟨hb, hℓe⟩ | ⟨hb, hℓe⟩
    · right
      refine ⟨by omega, by omega, ?_⟩
      rw [hwe b (by omega), hu_b, entry_of_length_lt V (by omega)]
    · left
      refine ⟨hb, ?_⟩
      rw [hwe b (by omega), hu_b]; omega
  · intro _ γ h1 h2
    rw [hwe γ (by omega), hu_other γ (by omega) (by omega)]
    refine ⟨rfl, ?_⟩
    rw [hmid γ h1 h2, hva]

end CovAux

/-- Proposition 16.11: the shape of a covering pair in `P(t)`. -/
theorem solution (t : ℕ) (V W : List ℕ) (hV : AppliedComb.ManyFaces.IsPartition t V)
    (hW : AppliedComb.ManyFaces.IsPartition t W) (hcov : AppliedComb.ManyFaces.Covers t V W) :
    W.length ≤ V.length + 1 ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ W.length ∧
        (∀ α : ℕ, 1 ≤ α → α < i →
          AppliedComb.ManyFaces.entry V α = AppliedComb.ManyFaces.entry W α) ∧
        (∀ β : ℕ, j < β → β ≤ V.length →
          AppliedComb.ManyFaces.entry V β = AppliedComb.ManyFaces.entry W β) ∧
        AppliedComb.ManyFaces.entry V i = 1 + AppliedComb.ManyFaces.entry W i ∧
        ((j ≤ V.length ∧
            AppliedComb.ManyFaces.entry W j = 1 + AppliedComb.ManyFaces.entry V j) ∨
          (j = W.length ∧ W.length = V.length + 1 ∧ AppliedComb.ManyFaces.entry W j = 1)) ∧
        (i + 1 < j → ∀ γ : ℕ, i < γ → γ < j →
          AppliedComb.ManyFaces.entry W γ = AppliedComb.ManyFaces.entry V γ ∧
            AppliedComb.ManyFaces.entry V γ = AppliedComb.ManyFaces.entry V i - 1) :=
  CovAux.covers_main hV hW hcov
