-- Prove2me | solution 1 for AppliedComb.ManyFaces.gale_ryser
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:03:32.692579+00:00
-- url     : https://prove2.me/submissions/4cfcff91-1c06-425e-b28a-16eae56a3305

import Mathlib
import Definitions.Def_AppliedComb_ManyFaces_partitionDominance
import Definitions.Def_AppliedComb_ManyFaces_dualPartition
import Definitions.Def_AppliedComb_ManyFaces_zeroOneMatrix

open Finset
open AppliedComb.ManyFaces

namespace GRAux

/-- The `k` rows with largest `r`-value. -/
lemma exists_top {m : ℕ} (r : Fin m → ℕ) : ∀ k : ℕ, k ≤ m →
    ∃ T : Finset (Fin m), T.card = k ∧ ∀ i ∈ T, ∀ i' ∉ T, r i' ≤ r i := by
  intro k
  induction k with
  | zero => intro _; exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨T, hT, hTmax⟩ := ih (by omega)
    have hne : (Tᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]; omega
    obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image Tᶜ r hne
    refine ⟨insert i0 T, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simpa using hi0), hT]
    · intro i hi i' hi'
      rw [Finset.mem_insert] at hi
      rw [Finset.mem_insert, not_or] at hi'
      rcases hi with rfl | hi
      · exact hmax i' (by simpa using hi'.2)
      · exact hTmax i hi i' hi'.2


/-- Gale–Ryser existence, by induction on the number of columns (columns as finsets of rows). -/
lemma gr_exists {m : ℕ} : ∀ (n : ℕ) (r : Fin m → ℕ) (c : ℕ → ℕ),
    (∀ a b, a ≤ b → b < n → c b ≤ c a) →
    ∑ i, r i = ∑ j ∈ range n, c j →
    (∀ k, k ≤ n → ∑ j ∈ range k, c j ≤ ∑ i, min (r i) k) →
    ∃ S : ℕ → Finset (Fin m), (∀ j < n, (S j).card = c j) ∧
      ∀ i, ((range n).filter (fun j => i ∈ S j)).card = r i := by
  intro n
  induction n with
  | zero =>
    intro r c _ hsum _
    refine ⟨fun _ => ∅, by simp, fun i => ?_⟩
    simp only [range_zero, sum_empty] at hsum
    have : r i = 0 := Finset.sum_eq_zero_iff.mp hsum i (mem_univ i)
    simp [this]
  | succ n ih =>
    intro r c hanti hsum hGR
    set P : Finset (Fin m) := univ.filter (fun i => 1 ≤ r i) with hPdef
    have hP : ∑ i, min (r i) 1 = P.card := by
      rw [hPdef, Finset.card_filter]
      refine sum_congr rfl fun i _ => ?_
      split_ifs <;> omega
    have h0 : c 0 ≤ P.card := by
      have := hGR 1 (by omega)
      simpa [hP] using this
    have hcn : c n ≤ c 0 := hanti 0 n (Nat.zero_le _) (by omega)
    have hPm : P.card ≤ m := by simpa using Finset.card_le_univ P
    obtain ⟨T, hTcard, hTmax⟩ := exists_top r (c n) (by omega)
    have hTpos : ∀ i ∈ T, 1 ≤ r i := by
      intro i hi
      by_contra h0'
      have hr0 : r i = 0 := by omega
      have hsub : P ⊆ T.erase i := by
        intro i' hi'
        rw [mem_erase]
        have hi'1 : 1 ≤ r i' := (mem_filter.mp hi').2
        refine ⟨?_, ?_⟩
        · rintro rfl; omega
        · by_contra hnT
          have := hTmax i hi i' hnT
          omega
      have h3 := card_le_card hsub
      rw [card_erase_of_mem hi] at h3
      have h4 : 0 < T.card := card_pos.mpr ⟨i, hi⟩
      omega
    set r' : Fin m → ℕ := fun i => if i ∈ T then r i - 1 else r i with hr'
    have hindsum : ∑ i, (if i ∈ T then 1 else 0) = T.card := by
      rw [Finset.sum_boole]; simp
    have h1 : ∑ i, (r' i + if i ∈ T then 1 else 0) = ∑ i, r i := by
      refine sum_congr rfl fun i _ => ?_
      by_cases hi : i ∈ T
      · have := hTpos i hi
        simp only [hr', hi, if_true]; omega
      · simp [hr', hi]
    rw [sum_add_distrib, hindsum, hTcard] at h1
    rw [sum_range_succ] at hsum
    have hsum' : ∑ i, r' i = ∑ j ∈ range n, c j := by omega
    have hGR' : ∀ k, k ≤ n → ∑ j ∈ range k, c j ≤ ∑ i, min (r' i) k := by
      intro k hk
      by_cases hA : ∀ i, k + 1 ≤ r i → i ∈ T
      · have key : ∀ i, min (r' i) k + (if i ∈ T then 1 else 0) = min (r i) (k + 1) := by
          intro i
          by_cases hi : i ∈ T
          · have := hTpos i hi
            simp only [hr', hi, if_true]; omega
          · have : r i ≤ k := by
              by_contra h; exact hi (hA i (by omega))
            simp only [hr', hi, if_false]; omega
        have h5 : ∑ i, (min (r' i) k + if i ∈ T then 1 else 0) = ∑ i, min (r i) (k + 1) :=
          sum_congr rfl fun i _ => key i
        rw [sum_add_distrib, hindsum, hTcard] at h5
        have h6 := hGR (k + 1) (by omega)
        rw [sum_range_succ] at h6
        have h7 : c n ≤ c k := hanti k n hk (by omega)
        omega
      · push Not at hA
        obtain ⟨i0, hi0, hi0T⟩ := hA
        have hbig : ∀ i ∈ T, k + 1 ≤ r i := fun i hi =>
          hi0.trans (hTmax i hi i0 hi0T)
        have : ∀ i, min (r' i) k = min (r i) k := by
          intro i
          by_cases hi : i ∈ T
          · have := hbig i hi
            simp only [hr', hi, if_true]; omega
          · simp [hr', hi]
        rw [sum_congr rfl fun i _ => this i]
        exact hGR k (by omega)
    obtain ⟨S', hS'card, hS'row⟩ := ih r' c
      (fun a b hab hb => hanti a b hab (by omega)) hsum' hGR'
    refine ⟨fun j => if j = n then T else S' j, ?_, ?_⟩
    · intro j hj
      by_cases hjn : j = n
      · subst hjn; simpa using hTcard
      · simp only [hjn, if_false]; exact hS'card j (by omega)
    · intro i
      rw [Finset.range_add_one, filter_insert]
      have hfil : ((range n).filter (fun j => i ∈ (if j = n then T else S' j))) =
          (range n).filter (fun j => i ∈ S' j) := by
        refine filter_congr fun j hj => ?_
        have : j ≠ n := by have := mem_range.mp hj; omega
        simp [this]
      rw [hfil]
      have hnot : n ∉ (range n).filter (fun j => i ∈ S' j) := by simp
      by_cases hi : i ∈ T
      · simp only [if_true, hi]
        rw [card_insert_of_notMem hnot, hS'row i]
        have := hTpos i hi
        simp only [hr', hi, if_true]; omega
      · simp only [if_true, hi, if_false]
        rw [hS'row i]
        simp [hr', hi]



lemma take_sum_eq_range (L : List ℕ) : ∀ k : ℕ, (L.take k).sum = ∑ j ∈ range k, L.getD j 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ← ih]
    by_cases hk : k < L.length
    · rw [List.sum_take_succ L k hk]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    · have h1 : L.length ≤ k := not_lt.mp hk
      rw [List.take_of_length_le h1, List.take_of_length_le (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]

lemma sum_ite_lt (a N : ℕ) : ∑ j ∈ range N, (if j + 1 ≤ a then 1 else 0) = min a N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

lemma countP_sum (R : List ℕ) (N : ℕ) :
    ∑ j ∈ range N, R.countP (fun v => decide (j + 1 ≤ v)) = (R.map (fun v => min v N)).sum := by
  induction R with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    rw [sum_add_distrib, ih]
    have := sum_ite_lt a N
    simp only [decide_eq_true_eq] at *
    rw [this]; ring


lemma sum_map_range (f : ℕ → ℕ) : ∀ N : ℕ, ((List.range N).map f).sum = ∑ j ∈ range N, f j := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

lemma le_headD {R : List ℕ} (hR : R.Pairwise (· ≥ ·)) : ∀ v ∈ R, v ≤ R.headD 0 := by
  cases R with
  | nil => simp
  | cons a l =>
    intro v hv
    rw [List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp
    · simpa using (List.pairwise_cons.mp hR).1 v hv

lemma dual_take_sum {R : List ℕ} (hR : R.Pairwise (· ≥ ·)) (k : ℕ) :
    ((dual R).take k).sum = (R.map (fun v => min v k)).sum := by
  unfold dual
  rw [← List.map_take, List.take_range, sum_map_range, countP_sum]
  congr 1
  refine List.map_congr_left fun v hv => ?_
  have := le_headD hR v hv
  omega

lemma dual_length (R : List ℕ) : (dual R).length = R.headD 0 := by simp [dual]


lemma sum_fin_eq (R : List ℕ) (g : ℕ → ℕ) :
    ∑ i : Fin R.length, g (R.get i) = (R.map g).sum := by
  induction R with
  | nil => simp
  | cons a l ih => simp [Fin.sum_univ_succ]

lemma getD_anti {C : List ℕ} (hC : C.Pairwise (· ≥ ·)) :
    ∀ a b, a ≤ b → b < C.length → C.getD b 0 ≤ C.getD a 0 := by
  intro a b hab hb
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have := List.pairwise_iff_getElem.mp hC a b (by omega) hb hlt
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb,
      List.getElem?_eq_getElem (show a < C.length by omega)] using this

lemma gr_of_dominates {t : ℕ} {R C : List ℕ} (hR : IsPartition t R) (hC : IsPartition t C)
    (hd : Dominates (dual R) C) : ∃ M : Matrix (Fin R.length) (Fin C.length) ℕ,
      IsZeroOneMatrixWithSums R C M := by
  set n := C.length with hn
  set r : Fin R.length → ℕ := fun i => R.get i with hr
  set c : ℕ → ℕ := fun j => C.getD j 0 with hc
  have hsumr : ∑ i, r i = t := by
    have := sum_fin_eq R (fun v => v)
    simp only [List.map_id'] at this
    rw [hr]; simp only; rw [this]; exact hR.2.2
  have hsumc : ∑ j ∈ range n, c j = t := by
    have := take_sum_eq_range C n
    rw [hn, List.take_length] at this
    rw [hc]; simp only; rw [← this]; exact hC.2.2
  have hGR : ∀ k, k ≤ n → ∑ j ∈ range k, c j ≤ ∑ i, min (r i) k := by
    intro k hk
    have e1 : ∑ i, min (r i) k = (R.map (fun v => min v k)).sum := sum_fin_eq R (fun v => min v k)
    rw [e1, ← take_sum_eq_range C k]
    by_cases hk' : 1 ≤ k ∧ k ≤ (dual R).length
    · have := hd.2 k hk'.1 hk'.2
      rw [dual_take_sum hR.1] at this
      exact this
    · have htot : (C.take k).sum ≤ t := by
        have := List.sum_take_add_sum_drop C k
        rw [hC.2.2] at this; omega
      by_cases hk0 : k = 0
      · subst hk0; simp
      · have hlt : (dual R).length < k := by omega
        rw [dual_length] at hlt
        have hmap : R.map (fun v => min v k) = R := by
          conv_rhs => rw [← List.map_id R]
          refine List.map_congr_left fun v hv => ?_
          have := le_headD hR.1 v hv
          simp only [id]; omega
        rw [hmap, hR.2.2]; exact htot
  obtain ⟨S, hScard, hSrow⟩ := gr_exists n r c
    (fun a b hab hb => getD_anti hC.1 a b hab hb) (by rw [hsumr, hsumc]) hGR
  refine ⟨Matrix.of fun i j => if i ∈ S j.val then 1 else 0, ?_, ?_, ?_⟩
  · intro i j; simp only [Matrix.of_apply]; split_ifs <;> simp
  · intro i
    simp only [Matrix.of_apply]
    calc ∑ j : Fin n, (if i ∈ S j.val then 1 else 0)
        = ∑ j ∈ range n, (if i ∈ S j then 1 else 0) := by
          rw [Finset.sum_range (fun j => if i ∈ S j then 1 else 0)]
      _ = ((range n).filter (fun j => i ∈ S j)).card := by rw [Finset.card_filter]
      _ = r i := hSrow i
  · intro j
    simp only [Matrix.of_apply]
    have h1 : ∑ i : Fin R.length, (if i ∈ S j.val then 1 else 0) = (S j.val).card := by
      rw [Finset.sum_boole]; simp
    rw [h1, hScard j.val j.2]
    simp [hc, List.getD_eq_getElem?_getD]


lemma headD_eq_getD (R : List ℕ) : R.headD 0 = R.getD 0 0 := by cases R <;> simp

lemma dominates_of_matrix {R C : List ℕ} (hR : R.Pairwise (· ≥ ·))
    (M : Matrix (Fin R.length) (Fin C.length) ℕ) (hM : IsZeroOneMatrixWithSums R C M) :
    Dominates (dual R) C := by
  obtain ⟨h01, hrow, hcol⟩ := hM
  have hM1 : ∀ i j, M i j ≤ 1 := fun i j => by rcases h01 i j with h | h <;> omega
  have hh : R.headD 0 ≤ C.length := by
    by_cases hR0 : 0 < R.length
    · rw [headD_eq_getD]
      have h0 := hrow ⟨0, hR0⟩
      have : R.getD 0 0 = R.get ⟨0, hR0⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hR0]
      rw [this, ← h0]
      calc ∑ j, M ⟨0, hR0⟩ j ≤ ∑ j : Fin C.length, 1 := sum_le_sum fun j _ => hM1 _ j
        _ = C.length := by simp
    · have : R = [] := List.length_eq_zero_iff.mp (by omega)
      subst this; simp
  refine ⟨by rw [dual_length]; exact hh, ?_⟩
  intro j hj1 hjh
  rw [dual_length] at hjh
  have hjn : j ≤ C.length := hjh.trans hh
  rw [dual_take_sum hR, take_sum_eq_range]
  set g : Fin R.length → ℕ → ℕ := fun i col => if h : col < C.length then M i ⟨col, h⟩ else 0 with hg
  have hg1 : ∀ i col, g i col ≤ 1 := by
    intro i col; simp only [hg]; split_ifs
    · exact hM1 _ _
    · exact Nat.zero_le _
  have hcol' : ∀ col < C.length, C.getD col 0 = ∑ i, g i col := by
    intro col hcol0
    have := hcol ⟨col, hcol0⟩
    simp only [hg, hcol0, dite_true]
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcol0]
  have hrow' : ∀ i, ∑ col ∈ range C.length, g i col = R.get i := by
    intro i
    rw [← hrow i, Finset.sum_range (fun col => g i col)]
    refine sum_congr rfl fun col _ => ?_
    simp [hg, col.2]
  calc ∑ col ∈ range j, C.getD col 0
      = ∑ col ∈ range j, ∑ i, g i col := by
        refine sum_congr rfl fun col hcol0 => hcol' col ?_
        have := mem_range.mp hcol0; omega
    _ = ∑ i, ∑ col ∈ range j, g i col := Finset.sum_comm
    _ ≤ ∑ i, min (R.get i) j := by
        refine sum_le_sum fun i _ => le_min ?_ ?_
        · rw [← hrow' i]
          exact sum_le_sum_of_subset (range_subset_range.mpr hjn)
        · calc ∑ col ∈ range j, g i col ≤ ∑ col ∈ range j, 1 :=
              sum_le_sum fun col _ => hg1 i col
            _ = j := by simp
    _ = (R.map (fun v => min v j)).sum := sum_fin_eq R (fun v => min v j)

end GRAux

/-- Theorem 16.12 (Gale–Ryser). -/
theorem solution (t : ℕ) (ht : 0 < t) (R C : List ℕ)
    (hR : AppliedComb.ManyFaces.IsPartition t R)
    (hC : AppliedComb.ManyFaces.IsPartition t C) :
    (∃ M : Matrix (Fin R.length) (Fin C.length) ℕ,
        AppliedComb.ManyFaces.IsZeroOneMatrixWithSums R C M) ↔
      AppliedComb.ManyFaces.Dominates (AppliedComb.ManyFaces.dual R) C :=
  ⟨fun ⟨M, hM⟩ => GRAux.dominates_of_matrix hR.1 M hM,
    fun hd => GRAux.gr_of_dominates hR hC hd⟩
