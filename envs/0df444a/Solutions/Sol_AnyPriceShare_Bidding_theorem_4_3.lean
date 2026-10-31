-- Prove2me | solution 1 for AnyPriceShare.Bidding.theorem_4_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:59:22.953916+00:00
-- url     : https://prove2.me/submissions/b23c6705-ec3f-4f59-a78b-9cdbb3373237
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game
import Theorems.Thm_AnyPriceShare_Bidding_lemma_4_6
import Theorems.Thm_AnyPriceShare_Bidding_lemma_D_3

open AnyPriceShare.Bidding

namespace APST43Sol

theorem sort_eq_cons_max {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S)
    (hmax : ∀ j' ∈ S, u j' ≤ u j) :
    (S.val.map u).sort (· ≥ ·) = u j :: ((S.erase j).val.map u).sort (· ≥ ·) := by
  have hval : S.val = j ::ₘ (S.erase j).val := by
    rw [Finset.erase_val, Multiset.cons_erase (by simpa using hj)]
  rw [hval, Multiset.map_cons]
  apply Multiset.sort_cons
  intro b hb
  obtain ⟨j', hj', rfl⟩ := Multiset.mem_map.1 hb
  have : j' ∈ S.erase j := hj'
  exact hmax j' (Finset.mem_of_mem_erase this)

theorem rankedValue_one {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S)
    (hmax : ∀ j' ∈ S, u j' ≤ u j) : rankedValue u S 1 = u j := by
  simp [rankedValue, sort_eq_cons_max u S j hj hmax]

theorem rankedValue_succ {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S)
    (hmax : ∀ j' ∈ S, u j' ≤ u j) (k : ℕ) (hk : 1 ≤ k) :
    rankedValue u S (k + 1) = rankedValue u (S.erase j) k := by
  unfold rankedValue
  rw [if_neg (by omega), if_neg (by omega), sort_eq_cons_max u S j hj hmax]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp

theorem rankedValue_le_max {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (S : Finset (Fin m))
    (j : Fin m) (hmax : ∀ j' ∈ S, u j' ≤ u j) (k : ℕ) : rankedValue u S k ≤ u j := by
  unfold rankedValue
  split_ifs
  · exact hu j
  · rw [List.getD_eq_getElem?_getD]
    cases hget : ((S.val.map u).sort (· ≥ ·))[k - 1]? with
    | none => simpa using hu j
    | some a =>
      have ha : a ∈ (S.val.map u).sort (· ≥ ·) := List.mem_of_getElem? hget
      rw [Multiset.mem_sort, Multiset.mem_map] at ha
      obtain ⟨j', hj', rfl⟩ := ha
      simpa using hmax j' (by simpa using hj')

theorem rankedValue_of_card_lt {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (k : ℕ)
    (hk : S.card < k) : rankedValue u S k = 0 := by
  unfold rankedValue
  split_ifs
  · rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · rw [Multiset.length_sort, Multiset.card_map, Finset.card_val]; omega

/-- If fewer than `k` items of `S` are gone, a surviving item is worth at least the `k`-th
ranked value. -/
theorem ranked_survivor {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) :
    ∀ k : ℕ, 1 ≤ k → ∀ S R : Finset (Fin m), R ⊆ S → (S \ R).card < k → k ≤ S.card →
      ∃ j ∈ R, rankedValue u S k ≤ u j := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro S R hRS hcard hS
    have hSR : S \ R = ∅ := Finset.card_eq_zero.1 (by omega)
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨j, hj, hmax⟩ := S.exists_max_image u hSne
    refine ⟨j, ?_, (rankedValue_one u S j hj hmax).le⟩
    by_contra hjR
    have : j ∈ S \ R := Finset.mem_sdiff.2 ⟨hj, hjR⟩
    rw [hSR] at this; simp at this
  | succ k hk ih =>
    intro S R hRS hcard hS
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨j, hj, hmax⟩ := S.exists_max_image u hSne
    by_cases hjR : j ∈ R
    · exact ⟨j, hjR, rankedValue_le_max u hu S j hmax _⟩
    · rw [rankedValue_succ u S j hj hmax k hk]
      have hRS' : R ⊆ S.erase j := fun x hx =>
        Finset.mem_erase.2 ⟨fun h => hjR (h ▸ hx), hRS hx⟩
      have hsd : (S.erase j) \ R = (S \ R).erase j := by
        ext x; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto
      have hjSR : j ∈ S \ R := Finset.mem_sdiff.2 ⟨hj, hjR⟩
      refine ih (S.erase j) R hRS' ?_ ?_
      · rw [hsd, Finset.card_erase_of_mem hjSR]; omega
      · rw [Finset.card_erase_of_mem hj]; omega


theorem budget_snoc {n m : ℕ} (b : Fin n → ℝ) (h : List (Round n m)) (r : Round n m) (k : Fin n) :
    budget b (h ++ [r]) k =
      budget b h k - (if r.winner = k then (r.taken.card : ℝ) * r.bids k else 0) := by
  simp only [budget, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

theorem take_succ' {α : Type*} (l : List α) (t : ℕ) (ht : t < l.length) :
    l.take (t + 1) = l.take t ++ [l[t]] := by
  exact List.take_succ_eq_append_getElem ht

theorem budget_take_nonneg {n m : ℕ} (b : Fin n → ℝ) (hb : ∀ k, 0 ≤ b k) (h : List (Round n m))
    (hp : ValidPlay b h) : ∀ t ≤ h.length, ∀ k, 0 ≤ budget b (h.take t) k := by
  intro t
  induction t with
  | zero => intro _ k; simp [budget, hb k]
  | succ t ih =>
    intro ht k
    have ht' : t < h.length := by omega
    rw [take_succ' h t ht', budget_snoc]
    have hr := hp t ht'
    have := ih ht'.le k
    simp only [List.get_eq_getElem] at hr
    split_ifs with hw
    · subst hw; have := hr.2.2.2.2; linarith
    · linarith

theorem budget_nonneg {n m : ℕ} (b : Fin n → ℝ) (hb : ∀ k, 0 ≤ b k) (h : List (Round n m))
    (hp : ValidPlay b h) (k : Fin n) : 0 ≤ budget b h k := by
  have := budget_take_nonneg b hb h hp h.length le_rfl k
  rwa [List.take_length] at this

theorem total_paid {n m : ℕ} (b : Fin n → ℝ) (h : List (Round n m)) :
    ∑ k, (b k - budget b h k) = (h.map fun r => (r.taken.card : ℝ) * r.bids r.winner).sum := by
  induction h with
  | nil => simp [budget]
  | cons r h ih =>
    have e : ∀ k, b k - budget b (r :: h) k =
        (if r.winner = k then (r.taken.card : ℝ) * r.bids k else 0) + (b k - budget b h k) := by
      intro k; simp only [budget, List.map_cons, List.sum_cons]; ring
    simp only [e, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [Finset.sum_ite_eq]
    simp

theorem removed_card {n m : ℕ} (h : List (Round n m)) :
    (((Finset.univ \ remaining h).card : ℕ) : ℝ) ≤ (h.map fun r => (r.taken.card : ℝ)).sum := by
  induction h with
  | nil => simp [remaining]
  | cons r h ih =>
    have hsub : Finset.univ \ remaining (r :: h) ⊆ r.taken ∪ (Finset.univ \ remaining h) := by
      intro j hj
      simp only [remaining, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and,
        List.mem_cons, forall_eq_or_imp, not_and, not_forall, not_not, Finset.mem_union] at hj ⊢
      by_cases hjr : j ∈ r.taken
      · exact Or.inl hjr
      · exact Or.inr (hj hjr)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le r.taken (Finset.univ \ remaining h)
    simp only [List.map_cons, List.sum_cons]
    have : ((Finset.univ \ remaining (r :: h)).card : ℝ) ≤
        (r.taken.card : ℝ) + ((Finset.univ \ remaining h).card : ℝ) := by
      exact_mod_cast h1.trans h2
    linarith

/-- The strategy for the ranked item (proof of Theorem 4.3): bid the whole budget and take a
most valuable remaining item. -/
noncomputable def rankedStrat {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    Strategy n m := fun h =>
  (budget b h i, if hR : (remaining h).Nonempty then
    {Classical.choose ((remaining h).exists_max_image u hR)} else ∅)

theorem rankedStrat_spec {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n)
    (h : List (Round n m)) (hR : (remaining h).Nonempty) :
    ∃ j ∈ remaining h, (∀ j' ∈ remaining h, u j' ≤ u j) ∧ (rankedStrat u b i h).2 = {j} := by
  have := Classical.choose_spec ((remaining h).exists_max_image u hR)
  exact ⟨_, this.1, this.2, by simp [rankedStrat, dif_pos hR]⟩

theorem addVal_nonneg {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (S : Finset (Fin m)) :
    0 ≤ addVal u S := Finset.sum_nonneg (fun j _ => hu j)

theorem ranked_guarantee {n m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n) :
    Guarantees b (rankedStrat u b i) i u (rankedValue u Finset.univ ⌊1 / b i⌋₊) := by
  classical
  have hb0 : ∀ k, 0 ≤ b k := fun k => (hb k).le
  constructor
  · intro h hp _ hne
    have hR : (remaining h).Nonempty := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨j, hj, -, hσ⟩ := rankedStrat_spec u b i h hR
    refine ⟨budget_nonneg b hb0 h hp i, le_rfl, ?_, ?_, ?_⟩
    · rw [hσ]; exact Finset.singleton_nonempty j
    · rw [hσ]; exact Finset.singleton_subset_iff.2 hj
    · rw [hσ]; simp [rankedStrat]
  · intro h hp hf hdone
    let P : ℕ → Prop := fun t => t = h.length ∨ ∃ ht : t < h.length, h[t].winner = i
    have hPex : ∃ t, P t := ⟨h.length, Or.inl rfl⟩
    set t0 := Nat.find hPex with ht0def
    have ht0le : t0 ≤ h.length := Nat.find_min' hPex (Or.inl rfl)
    have hbefore : ∀ s < t0, ∃ hs : s < h.length, h[s].winner ≠ i := by
      intro s hs
      have hns := Nat.find_min hPex hs
      simp only [P, not_or, not_exists] at hns
      have hsl : s < h.length := by omega
      exact ⟨hsl, hns.2 hsl⟩
    -- agent `i`'s budget is untouched before round `t0`
    have hbud : ∀ s ≤ t0, budget b (h.take s) i = b i := by
      intro s
      induction s with
      | zero => intro _; simp [budget]
      | succ s ih =>
        intro hs
        obtain ⟨hsl, hw⟩ := hbefore s (by omega)
        rw [take_succ' h s hsl, budget_snoc, ih (by omega), if_neg hw, sub_zero]
    -- accounting: every item taken before `t0` cost at least `b i`
    set h' := h.take t0 with hh'
    have hround : ∀ r ∈ h', (r.taken.card : ℝ) * b i ≤ (r.taken.card : ℝ) * r.bids r.winner := by
      intro r hr
      obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hr
      have hs' : s < t0 := by simp [hh'] at hs; omega
      obtain ⟨hsl, -⟩ := hbefore s hs'
      have hbid := (hf s hsl).1
      have hvr := (hp s hsl).2.1 i
      simp only [List.get_eq_getElem] at hbid hvr
      rw [List.getElem_take]
      have : (h[s]).bids i = b i := by
        rw [hbid]; simp only [rankedStrat]; exact hbud s hs'.le
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      linarith
    have hpaid := total_paid b h'
    have hsum_le : ∑ k, budget b h' k ≥ budget b h' i :=
      Finset.single_le_sum (fun k _ => budget_take_nonneg b hb0 h hp t0 ht0le k)
        (Finset.mem_univ i)
    have hbi : budget b h' i = b i := hbud t0 le_rfl
    have hN : (h'.map fun r => (r.taken.card : ℝ)).sum * b i ≤ 1 - b i := by
      rw [← List.sum_map_mul_right]
      have h1 := List.sum_le_sum hround
      rw [Finset.sum_sub_distrib, hsum] at hpaid
      linarith
    have hrem := removed_card h'
    set K := ⌊1 / b i⌋₊ with hK
    have hKbig : (Finset.univ \ remaining h').card + 1 ≤ K := by
      apply Nat.le_floor
      rw [le_div_iff₀ (hb i)]
      push_cast
      nlinarith [hb i]
    have hval0 := addVal_nonneg u hu (wonBy i h)
    rcases lt_or_eq_of_le ht0le with hlt | heq
    · -- agent `i` wins round `t0`
      have hwin : h[t0].winner = i := by
        have hspec := Nat.find_spec hPex
        rcases hspec with h1 | ⟨_, h2⟩
        · exact absurd h1 (by rw [← ht0def]; omega)
        · exact h2
      have hvr := hp t0 hlt
      simp only [List.get_eq_getElem] at hvr
      have htaken := (hf t0 hlt).2
      simp only [List.get_eq_getElem] at htaken
      have hRne : (remaining h').Nonempty := by
        obtain ⟨x, hx⟩ := hvr.2.2.1
        exact ⟨x, hvr.2.2.2.1 hx⟩
      obtain ⟨j, hj, hjmax, hσ⟩ := rankedStrat_spec u b i h' hRne
      have hjwon : j ∈ wonBy i h := by
        simp only [wonBy, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨h[t0], List.getElem_mem hlt, hwin, ?_⟩
        rw [htaken hwin, hσ]; exact Finset.mem_singleton_self j
      have hvj : u j ≤ addVal u (wonBy i h) :=
        Finset.single_le_sum (fun x _ => hu x) hjwon
      by_cases hKm : K ≤ (Finset.univ : Finset (Fin m)).card
      · obtain ⟨j', hj', hrv⟩ := ranked_survivor u hu K (by omega) Finset.univ (remaining h')
          (Finset.subset_univ _) (by omega) hKm
        linarith [hjmax j' hj']
      · rw [rankedValue_of_card_lt u _ K (by omega)]; exact hval0
    · -- agent `i` never wins: all items went to others
      rw [hh', heq, List.take_length, hdone, Finset.sdiff_empty] at hKbig
      rw [rankedValue_of_card_lt u _ K (by omega)]; exact hval0


theorem rule2_card {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) (h : List (Round n m))
    (h2 : lemmaD3Rule u b i h = 2) : 2 ≤ (remaining h).card := by
  unfold lemmaD3Rule at h2
  dsimp only at h2
  split_ifs at h2 with c1 c2 <;> first | omega | exact c2.1

open Classical in
/-- A strategy following the three rules of Lemma D.3 (ties among equally valuable items broken
by a fixed choice). -/
noncomputable def d3Strat {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    Strategy n m := fun h =>
  if hR : (remaining h).Nonempty then
    if lemmaD3DroppedOut u b i h then
      (0, {Classical.choose ((remaining h).exists_max_image u hR)})
    else if lemmaD3Rule u b i h = 1 then
      (budget b h i, {Classical.choose ((remaining h).exists_max_image u hR)})
    else if lemmaD3Rule u b i h = 2 then
      (if h2 : ((remaining h).erase
            (Classical.choose ((remaining h).exists_max_image u hR))).Nonempty then
        (budget b h i / 2, {Classical.choose ((remaining h).exists_max_image u hR),
          Classical.choose (((remaining h).erase
            (Classical.choose ((remaining h).exists_max_image u hR))).exists_max_image u h2)})
      else (0, ∅))
    else
      (rankedValue u (remaining h) 1 / addVal u (remaining h) * totalBudget b h,
        {Classical.choose ((remaining h).exists_max_image u hR)})
  else (0, ∅)

theorem d3Strat_spec {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    IsLemmaD3Strategy u b i (d3Strat u b i) := by
  classical
  intro h hne
  have hR : (remaining h).Nonempty := Finset.nonempty_iff_ne_empty.2 hne
  obtain ⟨hj1R, hj1max⟩ := Classical.choose_spec ((remaining h).exists_max_image u hR)
  set j1 := Classical.choose ((remaining h).exists_max_image u hR) with hj1
  have hx : u j1 = rankedValue u (remaining h) 1 := (rankedValue_one u _ j1 hj1R hj1max).symm
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hd
    simp only [d3Strat, dif_pos hR, if_pos hd, ← hj1]
    exact ⟨trivial, j1, hj1R, rfl⟩
  · intro hd h1
    simp only [d3Strat, dif_pos hR, if_neg hd, h1, if_true, ← hj1]
    exact ⟨j1, hj1R, hx, rfl⟩
  · intro hd h2
    have hc := rule2_card u b i h h2
    have he : ((remaining h).erase j1).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hj1R]; omega
    obtain ⟨hj2R, hj2max⟩ := Classical.choose_spec (((remaining h).erase j1).exists_max_image u he)
    set j2 := Classical.choose (((remaining h).erase j1).exists_max_image u he) with hj2
    have hy : u j2 = rankedValue u (remaining h) 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, rankedValue_succ u _ j1 hj1R hj1max 1 le_rfl,
        rankedValue_one u _ j2 hj2R hj2max]
    simp only [d3Strat, dif_pos hR, if_neg hd, h2, ← hj1]
    simp only [show (2 : ℕ) ≠ 1 by norm_num, if_false, if_true, dif_pos he, ← hj2]
    exact ⟨j1, hj1R, j2, Finset.mem_of_mem_erase hj2R, (Finset.ne_of_mem_erase hj2R).symm,
      hx, hy, rfl⟩
  · intro hd h3
    simp only [d3Strat, dif_pos hR, if_neg hd, h3, ← hj1]
    simp only [show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num, if_false]
    exact ⟨j1, hj1R, hx, rfl⟩

end APST43Sol

open APST43Sol in
theorem solution {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n) :
    ∃ σ : Strategy n m,
      Guarantees b σ i (v i)
        (max (max (3 / 5 * anyPrice (b i) (addVal (v i)) Finset.univ)
                  (1 / (2 - b i) * tps (b i) (v i) Finset.univ))
             (rankedValue (v i) Finset.univ ⌊1 / b i⌋₊)) := by
  obtain ⟨σ1, h1⟩ := lemma_4_6 (v i) (hv i) b hb hsum i
  have h2 := lemma_D_3 (v i) (hv i) b hb hsum i (d3Strat (v i) b i) (d3Strat_spec (v i) b i)
  have h3 := ranked_guarantee (v i) (hv i) b hb hsum i
  rcases max_choice (max (3 / 5 * anyPrice (b i) (addVal (v i)) Finset.univ)
      (1 / (2 - b i) * tps (b i) (v i) Finset.univ))
      (rankedValue (v i) Finset.univ ⌊1 / b i⌋₊) with e | e <;> rw [e]
  · rcases max_choice (3 / 5 * anyPrice (b i) (addVal (v i)) Finset.univ)
      (1 / (2 - b i) * tps (b i) (v i) Finset.univ) with e' | e' <;> rw [e']
    · exact ⟨σ1, h1⟩
    · exact ⟨_, h2⟩
  · exact ⟨_, h3⟩
