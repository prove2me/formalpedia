-- Prove2me | solution 1 for AnyPriceShare.Bidding.lemma_4_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T02:47:58.357591+00:00
-- url     : https://prove2.me/submissions/fd69b729-6bd5-4644-b2fc-66346690feab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game
import Theorems.Thm_AnyPriceShare_Bidding_lemma_4_7
import Theorems.Thm_AnyPriceShare_Bidding_proposition_3_2
import Theorems.Thm_AnyPriceShare_Bidding_proposition_3_7_proportional

open AnyPriceShare.Bidding

namespace APSL46Sol

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

theorem addVal_nonneg {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (S : Finset (Fin m)) :
    0 ≤ addVal u S := Finset.sum_nonneg (fun j _ => hu j)

theorem remaining_snoc {n m : ℕ} (h : List (Round n m)) (r : Round n m) :
    remaining (h ++ [r]) = remaining h \ r.taken := by
  ext j
  simp [remaining, or_imp, forall_and]

theorem mem_wonBy_snoc {n m : ℕ} (i : Fin n) (h : List (Round n m)) (r : Round n m)
    (j : Fin m) : j ∈ wonBy i (h ++ [r]) ↔ j ∈ wonBy i h ∨ (r.winner = i ∧ j ∈ r.taken) := by
  simp [wonBy, or_and_right, exists_or]

theorem not_mem_remaining_of_mem_wonBy {n m : ℕ} (i : Fin n) (h : List (Round n m)) (j : Fin m)
    (hj : j ∈ wonBy i h) : j ∉ remaining h := by
  simp only [wonBy, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨r, hr, -, hjr⟩ := hj
  simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not]
  exact ⟨r, hr, hjr⟩

theorem sum_paid_snoc {n m : ℕ} (b : Fin n → ℝ) (h : List (Round n m)) (r : Round n m) :
    ∑ k, (b k - budget b (h ++ [r]) k) =
      ∑ k, (b k - budget b h k) + (r.taken.card : ℝ) * r.bids r.winner := by
  simp only [budget_snoc, sub_sub_eq_add_sub, add_sub_right_comm _ _ (budget b h _)]
  rw [Finset.sum_add_distrib, add_comm, Finset.sum_ite_eq]
  simp [add_comm]

theorem addVal_union {m : ℕ} (u : Fin m → ℝ) (A B : Finset (Fin m)) (hAB : Disjoint A B) :
    addVal u (A ∪ B) = addVal u A + addVal u B := Finset.sum_union hAB

/-- The set whose supremum is the TPS. -/
theorem tps_bdd {m : ℕ} (u : Fin m → ℝ) (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) :
    BddAbove {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} := by
  refine ⟨β * ∑ j ∈ S, u j, fun z hz => ?_⟩
  simp only [Set.mem_ofPred_eq] at hz
  rw [← hz]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => min_le_left _ _) hβ.le

theorem tps_zero_mem {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (S : Finset (Fin m)) :
    (0 : ℝ) ∈ {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} := by
  simp only [Set.mem_ofPred_eq]
  rw [Finset.sum_eq_zero fun j _ => min_eq_right (hu j)]; simp

theorem tps_cont {m : ℕ} (u : Fin m → ℝ) (β : ℝ) (S : Finset (Fin m)) :
    Continuous fun z : ℝ => β * ∑ j ∈ S, min (u j) z := by
  fun_prop

theorem tps_mem {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) : β * ∑ j ∈ S, min (u j) (tps β u S) = tps β u S := by
  have hc : IsClosed {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} :=
    isClosed_eq (tps_cont u β S) continuous_id
  exact hc.csSup_mem ⟨0, tps_zero_mem u hu β S⟩ (tps_bdd u β hβ S)

theorem tps_nonneg {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) : 0 ≤ tps β u S :=
  le_csSup (tps_bdd u β hβ S) (tps_zero_mem u hu β S)

/-- Above the TPS the capped proportional share is strictly below the cap (intermediate value
theorem). -/
theorem tps_lt {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) (z : ℝ) (hz : tps β u S < z) : β * ∑ j ∈ S, min (u j) z < z := by
  by_contra hcon
  push Not at hcon
  set g : ℝ → ℝ := fun t => β * ∑ j ∈ S, min (u j) t - t with hg
  have hgc : Continuous g := (tps_cont u β S).sub continuous_id
  set b' := max z (β * ∑ j ∈ S, u j)
  have hzb : z ≤ b' := le_max_left _ _
  have hgz : 0 ≤ g z := by simp only [hg]; linarith
  have hgb : g b' ≤ 0 := by
    have : β * ∑ j ∈ S, min (u j) b' ≤ β * ∑ j ∈ S, u j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => min_le_left _ _) hβ.le
    simp only [hg]; linarith [le_max_right z (β * ∑ j ∈ S, u j)]
  obtain ⟨t, ⟨ht1, -⟩, ht⟩ :=
    intermediate_value_Icc' hzb hgc.continuousOn ⟨hgb, hgz⟩
  have hmem : t ∈ {z : ℝ | β * ∑ j ∈ S, min (u j) z = z} := by
    simp only [Set.mem_ofPred_eq]; simp only [hg] at ht; linarith
  have := le_csSup (tps_bdd u β hβ S) hmem
  unfold tps at hz
  linarith

theorem rule2_card {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) (h : List (Round n m))
    (h2 : lemmaD3Rule u b i h = 2) : 2 ≤ (remaining h).card := by
  unfold lemmaD3Rule at h2
  dsimp only at h2
  split_ifs at h2 with c1 c2 <;> first | omega | exact c2.1



theorem rankedValue_of_card_lt {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (k : ℕ)
    (hk : S.card < k) : rankedValue u S k = 0 := by
  unfold rankedValue
  split_ifs
  · rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · rw [Multiset.length_sort, Multiset.card_map, Finset.card_val]; omega

theorem rankedValue_nonneg {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (S : Finset (Fin m))
    (k : ℕ) : 0 ≤ rankedValue u S k := by
  unfold rankedValue
  split_ifs
  · exact le_rfl
  · rw [List.getD_eq_getElem?_getD]
    cases hget : ((S.val.map u).sort (· ≥ ·))[k - 1]? with
    | none => simp
    | some a =>
      have ha : a ∈ (S.val.map u).sort (· ≥ ·) := List.mem_of_getElem? hget
      rw [Multiset.mem_sort, Multiset.mem_map] at ha
      obtain ⟨j', _, rfl⟩ := ha
      simpa using hu j'

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

/-! ### Continuing the game as a two-agent game on the remaining items -/

theorem budget_append {n m : ℕ} (b : Fin n → ℝ) (h0 h : List (Round n m)) (k : Fin n) :
    budget b (h0 ++ h) k = budget b h0 k -
      (h.map fun r => if r.winner = k then (r.taken.card : ℝ) * r.bids k else 0).sum := by
  simp only [budget, List.map_append, List.sum_append]; ring

theorem sum_list_sum {n m : ℕ} (E : Finset (Fin n)) (h : List (Round n m))
    (f : Fin n → Round n m → ℝ) :
    ∑ k ∈ E, (h.map (f k)).sum = (h.map fun r => ∑ k ∈ E, f k r).sum := by
  induction h with
  | nil => simp
  | cons r h ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- The bid of the merged adversary: the winner's bid if an adversary wins, else `0`. -/
noncomputable def advBid {n m : ℕ} (i : Fin n) (r : Round n m) : ℝ :=
  if r.winner = i then 0 else r.bids r.winner

/-- A round of the real game seen in the two-agent game on the remaining items. -/
noncomputable def subRound {n m m' : ℕ} (i : Fin n) (ι : Fin m' → Fin m) (B : ℝ)
    (r : Round n m) : Round 2 m' :=
  ⟨![r.bids i / B, advBid i r / B], if r.winner = i then 0 else 1,
    Finset.univ.filter (fun a => ι a ∈ r.taken)⟩

noncomputable def subHist {n m m' : ℕ} (i : Fin n) (ι : Fin m' → Fin m) (B : ℝ)
    (h : List (Round n m)) : List (Round 2 m') := h.map (subRound i ι B)

/-- The real continuation of a strategy of the two-agent game. -/
noncomputable def contStrat {n m m' : ℕ} (i : Fin n) (ι : Fin m' ↪ Fin m) (B : ℝ)
    (σ' : Strategy 2 m') (h : List (Round n m)) : ℝ × Finset (Fin m) :=
  ((σ' (subHist i ι B h)).1 * B, (σ' (subHist i ι B h)).2.map ι)

theorem preimage_map {m m' : ℕ} (ι : Fin m' ↪ Fin m) (T : Finset (Fin m))
    (hT : ∀ j ∈ T, ∃ a, ι a = j) :
    (Finset.univ.filter (fun a => ι a ∈ T)).map ι = T := by
  ext j
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro hj; obtain ⟨a, rfl⟩ := hT j hj; exact ⟨a, hj, rfl⟩

theorem card_preimage' {m m' : ℕ} (ι : Fin m' ↪ Fin m) (T : Finset (Fin m))
    (hT : ∀ j ∈ T, ∃ a, ι a = j) :
    (Finset.univ.filter (fun a => ι a ∈ T)).card = T.card := by
  conv_rhs => rw [← preimage_map ι T hT]
  rw [Finset.card_map]

theorem filter_map_self {m m' : ℕ} (ι : Fin m' ↪ Fin m) (A : Finset (Fin m')) :
    Finset.univ.filter (fun a => ι a ∈ A.map ι) = A := by
  ext a; simp

theorem addVal_map {m m' : ℕ} (ι : Fin m' ↪ Fin m) (u : Fin m → ℝ) (A : Finset (Fin m')) :
    addVal (u ∘ ι) A = addVal u (A.map ι) := by
  simp [addVal, Finset.sum_map]

section transfer

variable {n m m' : ℕ} (b : Fin n → ℝ) (i : Fin n) (h0 : List (Round n m))
  (ι : Fin m' ↪ Fin m) (B : ℝ) (b2 : Fin 2 → ℝ)

theorem sub_budget0 (hB : B ≠ 0) (hb20 : b2 0 = budget b h0 i / B) (h : List (Round n m))
    (hsub : ∀ r ∈ h, ∀ j ∈ r.taken, ∃ a, ι a = j) :
    budget b2 (subHist i ι B h) 0 = budget b (h0 ++ h) i / B := by
  have key : ∀ g : List (Round n m), (∀ r ∈ g, ∀ j ∈ r.taken, ∃ a, ι a = j) →
      ((subHist i ι B g).map fun r => if r.winner = 0 then (r.taken.card : ℝ) * r.bids 0
        else 0).sum =
      (g.map fun r => if r.winner = i then (r.taken.card : ℝ) * r.bids i else 0).sum / B := by
    intro g
    induction g with
    | nil => simp [subHist]
    | cons r g ih =>
      intro hg
      simp only [subHist, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih (fun r' hr' => hg r' (List.mem_cons_of_mem _ hr')), add_div]
      congr 1
      simp only [subRound]
      by_cases hw : r.winner = i
      · simp only [hw, if_true, Matrix.cons_val_zero]
        rw [card_preimage' ι r.taken (hg r List.mem_cons_self)]
        ring
      · simp [hw]
  unfold budget
  rw [key h hsub, hb20, ← budget, budget_append, sub_div]

theorem sub_budget1 (hB : B ≠ 0) (hb21 : b2 1 = (∑ k ∈ Finset.univ.erase i, budget b h0 k) / B)
    (h : List (Round n m)) (hsub : ∀ r ∈ h, ∀ j ∈ r.taken, ∃ a, ι a = j) :
    budget b2 (subHist i ι B h) 1 = (∑ k ∈ Finset.univ.erase i, budget b (h0 ++ h) k) / B := by
  have key : ∀ g : List (Round n m), (∀ r ∈ g, ∀ j ∈ r.taken, ∃ a, ι a = j) →
      ((subHist i ι B g).map fun r => if r.winner = 1 then (r.taken.card : ℝ) * r.bids 1
        else 0).sum =
      (g.map fun r => ∑ k ∈ Finset.univ.erase i,
        if r.winner = k then (r.taken.card : ℝ) * r.bids k else 0).sum / B := by
    intro g
    induction g with
    | nil => simp [subHist]
    | cons r g ih =>
      intro hg
      simp only [subHist, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih (fun r' hr' => hg r' (List.mem_cons_of_mem _ hr')), add_div]
      congr 1
      rw [Finset.sum_ite_eq]
      simp only [subRound, Finset.mem_erase, Finset.mem_univ, and_true]
      by_cases hw : r.winner = i
      · simp [hw]
      · rw [if_pos hw]
        (simp [hw, advBid, card_preimage' ι r.taken (hg r List.mem_cons_self)]) <;> ring
  show b2 1 - ((subHist i ι B h).map fun r => if r.winner = 1 then (r.taken.card : ℝ) * r.bids 1
    else 0).sum = _
  rw [key h hsub, hb21]
  have : ∑ k ∈ Finset.univ.erase i, budget b (h0 ++ h) k = ∑ k ∈ Finset.univ.erase i, budget b h0 k
      - (h.map fun r => ∑ k ∈ Finset.univ.erase i,
        if r.winner = k then (r.taken.card : ℝ) * r.bids k else 0).sum := by
    simp only [budget_append, Finset.sum_sub_distrib]
    rw [sum_list_sum]
  rw [this, sub_div]

theorem mem_remaining_sub (hrange : ∀ j, j ∈ remaining h0 ↔ ∃ a, ι a = j)
    (h : List (Round n m)) (a : Fin m') :
    a ∈ remaining (subHist i ι B h) ↔ ι a ∈ remaining (h0 ++ h) := by
  have ha0 : ι a ∈ remaining h0 := (hrange _).2 ⟨a, rfl⟩
  simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and] at ha0 ⊢
  simp only [subHist, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    subRound, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_append]
  constructor
  · intro H r hr
    rcases hr with hr | hr
    · exact ha0 r hr
    · exact H r hr
  · intro H r hr; exact H r (Or.inr hr)

end transfer

theorem take_append_length_add {α : Type*} (l1 l2 : List α) (k : ℕ) :
    (l1 ++ l2).take (l1.length + k) = l1 ++ l2.take k := by
  simp [List.take_append]

/-- Transfer of a guarantee from the two-agent game on the remaining items to the real
continuation of the game after `h0`. -/
theorem transfer {n m m' : ℕ} (b : Fin n → ℝ) (hb0 : ∀ k, 0 ≤ b k) (i : Fin n)
    (h0 : List (Round n m)) (hp0 : ValidPlay b h0)
    (ι : Fin m' ↪ Fin m) (hrange : ∀ j, j ∈ remaining h0 ↔ ∃ a, ι a = j)
    (B : ℝ) (hBpos : 0 < B) (b2 : Fin 2 → ℝ) (hb20 : b2 0 = budget b h0 i / B)
    (hb21 : b2 1 = (∑ k ∈ Finset.univ.erase i, budget b h0 k) / B)
    (σ' : Strategy 2 m') (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (x : ℝ)
    (hG : Guarantees b2 σ' 0 (u ∘ ι) x) (h : List (Round n m))
    (hp : ValidPlay b (h0 ++ h))
    (hf : ∀ (k : ℕ) (hk : k < h.length), h[k].bids i = (contStrat i ι B σ' (h.take k)).1 ∧
      (h[k].winner = i → h[k].taken = (contStrat i ι B σ' (h.take k)).2)) :
    (remaining (h0 ++ h) ≠ ∅ → LegalMove b (h0 ++ h) i (contStrat i ι B σ' h)) ∧
    (remaining (h0 ++ h) = ∅ → x ≤ addVal u (wonBy i (h0 ++ h))) := by
  classical
  have hB : B ≠ 0 := hBpos.ne'
  -- the rounds after `h0`
  have hround : ∀ k (hk : k < h.length), ValidRound b (h0 ++ h.take k) h[k] := by
    intro k hk
    have := hp (h0.length + k) (by simp; omega)
    simp only [List.get_eq_getElem] at this
    rw [take_append_length_add] at this
    simpa [List.getElem_append_right (by omega : h0.length ≤ h0.length + k)] using this
  have hrem_sub : ∀ g : List (Round n m), remaining (h0 ++ g) ⊆ remaining h0 := by
    intro g j hj
    simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_append] at hj ⊢
    exact fun r hr => hj r (Or.inl hr)
  have htk : ∀ r ∈ h, ∀ j ∈ r.taken, ∃ a, ι a = j := by
    intro r hr j hj
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    have hv := hround k hk
    exact (hrange j).1 (hrem_sub _ (hv.2.2.2.1 hj))
  have htk' : ∀ k, ∀ r ∈ h.take k, ∀ j ∈ r.taken, ∃ a, ι a = j :=
    fun k r hr => htk r (List.mem_of_mem_take hr)
  have hbudnn : ∀ k ≤ h.length, ∀ a, 0 ≤ budget b (h0 ++ h.take k) a := by
    intro k hk a
    have := budget_take_nonneg b hb0 (h0 ++ h) hp (h0.length + k) (by simp; omega) a
    rwa [take_append_length_add] at this
  -- budgets of the two-agent game
  have hb0' : ∀ g, (∀ r ∈ g, ∀ j ∈ r.taken, ∃ a, ι a = j) →
      budget b2 (subHist i ι B g) 0 = budget b (h0 ++ g) i / B :=
    fun g hg => sub_budget0 b i h0 ι B b2 hB hb20 g hg
  have hb1' : ∀ g, (∀ r ∈ g, ∀ j ∈ r.taken, ∃ a, ι a = j) →
      budget b2 (subHist i ι B g) 1 = (∑ k ∈ Finset.univ.erase i, budget b (h0 ++ g) k) / B :=
    fun g hg => sub_budget1 b i h0 ι B b2 hB hb21 g hg
  have hremiff := mem_remaining_sub i h0 ι B hrange
  -- the two-agent history is a valid play followed by `σ'`
  have hvalid : ValidPlay b2 (subHist i ι B h) := by
    intro k hk
    simp only [subHist, List.length_map] at hk
    simp only [List.get_eq_getElem, subHist, List.getElem_map, ← List.map_take]
    have hv := hround k hk
    set r := h[k]
    set g := h.take k
    have hg := htk' k
    have hnn := hbudnn k hk.le
    have hB0 := hb0' g hg
    have hB1 := hb1' g hg
    rw [show List.map (subRound i ι B) g = subHist i ι B g from rfl]
    have hadv : 0 ≤ ∑ k ∈ Finset.univ.erase i, budget b (h0 ++ g) k :=
      Finset.sum_nonneg fun a _ => hnn a
    have hwle : r.winner ≠ i → r.bids r.winner ≤ ∑ k ∈ Finset.univ.erase i, budget b (h0 ++ g) k :=
      fun hw => le_trans (hv.1 r.winner).2
        (Finset.single_le_sum (fun a _ => hnn a) (Finset.mem_erase.2 ⟨hw, Finset.mem_univ _⟩))
    have hbi0 := (hv.1 i).1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a
      fin_cases a
      · simp only [subRound, Fin.zero_eta, Matrix.cons_val_zero]
        rw [hB0]
        exact ⟨div_nonneg hbi0 hBpos.le, div_le_div_of_nonneg_right (hv.1 i).2 hBpos.le⟩
      · simp only [subRound, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hB1]
        unfold advBid
        split_ifs with hw
        · simp only [zero_div]; exact ⟨le_rfl, div_nonneg hadv hBpos.le⟩
        · exact ⟨div_nonneg (hv.1 _).1 hBpos.le, div_le_div_of_nonneg_right (hwle hw) hBpos.le⟩
    · intro a
      fin_cases a
      · simp only [subRound, Fin.zero_eta, Matrix.cons_val_zero]
        split_ifs with hw
        · simp
        · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, advBid, if_neg hw]
          exact div_le_div_of_nonneg_right (hv.2.1 i) hBpos.le
      · simp only [subRound, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        split_ifs with hw
        · simp only [Matrix.cons_val_zero, advBid, if_pos hw, zero_div]
          exact div_nonneg hbi0 hBpos.le
        · simp
    · obtain ⟨j, hj⟩ := hv.2.2.1
      obtain ⟨a, rfl⟩ := htk r (List.getElem_mem hk) j hj
      exact ⟨a, by simp [subRound, hj]⟩
    · intro a ha
      simp only [subRound, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [hremiff]
      exact hv.2.2.2.1 ha
    · have hc := card_preimage' ι r.taken (htk r (List.getElem_mem hk))
      simp only [subRound]
      rw [hc]
      split_ifs with hw
      · simp only [Matrix.cons_val_zero]
        rw [hB0, ← hw]
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hBpos]
        have := hv.2.2.2.2; rw [hw] at this ⊢; exact this
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, advBid, if_neg hw]
        rw [hB1, mul_div_assoc', div_le_div_iff_of_pos_right hBpos]
        exact le_trans hv.2.2.2.2 (le_trans (le_refl _)
          (Finset.single_le_sum (fun a _ => hnn a) (Finset.mem_erase.2 ⟨hw, Finset.mem_univ _⟩)))
  have hfollow : FollowedBy σ' 0 (subHist i ι B h) := by
    intro k hk
    simp only [subHist, List.length_map] at hk
    simp only [List.get_eq_getElem, subHist, List.getElem_map, ← List.map_take]
    obtain ⟨h1, h2⟩ := hf k hk
    constructor
    · simp only [subRound, Matrix.cons_val_zero]
      rw [h1]; simp only [contStrat]; field_simp; rfl
    · intro hw
      simp only [subRound] at hw ⊢
      have hwi : h[k].winner = i := by
        by_contra hc; rw [if_neg hc] at hw; exact absurd hw (by decide)
      rw [h2 hwi]
      simp only [contStrat]
      exact filter_map_self ι _
  constructor
  · intro hne
    have hne' : remaining (subHist i ι B h) ≠ ∅ := by
      intro he
      apply hne
      ext j
      simp only [Finset.notMem_empty, iff_false]
      intro hj
      obtain ⟨a, rfl⟩ := (hrange j).1 (hrem_sub h hj)
      have : a ∈ remaining (subHist i ι B h) := (hremiff h a).2 hj
      rw [he] at this; simp at this
    have hL := hG.1 _ hvalid hfollow hne'
    have hB0 := hb0' h htk
    obtain ⟨l1, l2, l3, l4, l5⟩ := hL
    rw [hB0] at l2 l5
    refine ⟨mul_nonneg l1 hBpos.le, ?_, ?_, ?_, ?_⟩
    · simp only [contStrat]; rwa [le_div_iff₀ hBpos] at l2
    · simp only [contStrat]; exact l3.map
    · intro j hj
      simp only [contStrat, Finset.mem_map] at hj
      obtain ⟨a, ha, rfl⟩ := hj
      exact (hremiff h a).1 (l4 ha)
    · simp only [contStrat, Finset.card_map]
      rw [le_div_iff₀ hBpos] at l5
      linarith
  · intro hdone
    have hdone' : remaining (subHist i ι B h) = ∅ := by
      ext a
      simp only [Finset.notMem_empty, iff_false]
      intro ha
      have := (hremiff h a).1 ha
      rw [hdone] at this; simp at this
    have hV := hG.2 _ hvalid hfollow hdone'
    rw [addVal_map] at hV
    refine le_trans hV ?_
    unfold addVal
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => hu j)
    intro j hj
    simp only [Finset.mem_map, wonBy, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨a, ⟨r', hr', hw', ha⟩, rfl⟩ := hj
    simp only [subHist, List.mem_map] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    simp only [subRound, Finset.mem_filter, Finset.mem_univ, true_and] at hw' ha
    have hwi : r.winner = i := by
      by_contra hc; rw [if_neg hc] at hw'; exact absurd hw' (by decide)
    exact ⟨r, List.mem_append_right _ hr, hwi, ha⟩

/-! ### Equation (2): a packing for the remaining items -/

theorem greedy_prefix {m : ℕ} (u : Fin m → ℝ) (δ L : ℝ) (A : Finset (Fin m))
    (hA : ∀ e ∈ A, u e < δ) (c : ℝ) (hc : c < L) (hcA : L ≤ c + addVal u A) :
    ∃ A' ⊆ A, L ≤ c + addVal u A' ∧ c + addVal u A' < L + δ := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [addVal] at hcA; linarith
  | insert a A0 ha ih =>
    by_cases h0 : L ≤ c + addVal u A0
    · obtain ⟨A', hA', h1, h2⟩ := ih (fun e he => hA e (Finset.mem_insert_of_mem he)) h0
      exact ⟨A', hA'.trans (Finset.subset_insert _ _), h1, h2⟩
    · push Not at h0
      refine ⟨insert a A0, le_rfl, hcA, ?_⟩
      rw [addVal, Finset.sum_insert ha]
      have := hA a (Finset.mem_insert_self a A0)
      unfold addVal at h0
      linarith

/-- Splitting a bundle worth at least `z` whose items, and pairs of items, are worth less
than `3z/5` into two parts worth at least `2z/5` each (proof of Lemma 4.6). -/
theorem split_bundle {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (z : ℝ) (hz : 0 < z)
    (T : Finset (Fin m)) (hT : z ≤ addVal u T)
    (hsingle : ∀ e ∈ T, u e < 3 * z / 5)
    (hpair : ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → u e + u e' < 3 * z / 5) :
    ∃ C ⊆ T, 2 * z / 5 ≤ addVal u C ∧ 2 * z / 5 ≤ addVal u (T \ C) := by
  classical
  have hsd : ∀ C ⊆ T, addVal u (T \ C) = addVal u T - addVal u C := fun C hC => by
    unfold addVal; rw [Finset.sum_sdiff_eq_sub hC]
  suffices ∃ C ⊆ T, 2 * z / 5 ≤ addVal u C ∧ addVal u C ≤ 3 * z / 5 by
    obtain ⟨C, hC, h1, h2⟩ := this
    exact ⟨C, hC, h1, by rw [hsd C hC]; linarith⟩
  by_cases hA : ∃ e ∈ T, 2 * z / 5 ≤ u e
  · obtain ⟨e, he, hle⟩ := hA
    refine ⟨{e}, Finset.singleton_subset_iff.2 he, ?_, ?_⟩ <;> simp only [addVal,
      Finset.sum_singleton]
    · exact hle
    · exact (hsingle e he).le
  push Not at hA
  by_cases hB : ∃ e ∈ T, ∃ e' ∈ T, e ≠ e' ∧ 2 * z / 5 ≤ u e + u e'
  · obtain ⟨e, he, e', he', hne, hle⟩ := hB
    refine ⟨{e, e'}, Finset.insert_subset he (Finset.singleton_subset_iff.2 he'), ?_, ?_⟩ <;>
      simp only [addVal, Finset.sum_pair hne]
    · exact hle
    · exact (hpair e he e' he' hne).le
  push Not at hB
  have hTne : T.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; subst h; simp [addVal] at hT; linarith
  obtain ⟨e0, he0, he0max⟩ := T.exists_max_image u hTne
  have hsmall : ∀ a ∈ T.erase e0, u a < z / 5 := by
    intro a ha
    have hne : a ≠ e0 := Finset.ne_of_mem_erase ha
    have haT := Finset.mem_of_mem_erase ha
    have h1 := hB a haT e0 he0 hne
    have h2 := he0max a haT
    linarith
  have hsplitT : addVal u T = u e0 + addVal u (T.erase e0) := by
    unfold addVal; rw [← Finset.add_sum_erase T u he0]
  obtain ⟨A', hA', h1, h2⟩ := greedy_prefix u (z / 5) (2 * z / 5) (T.erase e0) hsmall (u e0)
    (hA e0 he0) (by rw [← hsplitT]; linarith)
  have he0A' : e0 ∉ A' := fun h => by simpa using hA' h
  refine ⟨insert e0 A', Finset.insert_subset he0 (hA'.trans (Finset.erase_subset _ _)), ?_, ?_⟩
  · rw [addVal, Finset.sum_insert he0A']; unfold addVal at h1; linarith
  · rw [addVal, Finset.sum_insert he0A']; unfold addVal at h2; linarith

/-- The packing set of Definition 3.1. -/
def Zset {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) (S : Finset (Fin m)) : Set ℝ :=
  {z : ℝ | ∃ lam : Finset (Fin m) → ℝ,
    (∑ T ∈ S.powerset, lam T = 1) ∧
    (∀ T ∈ S.powerset, 0 ≤ lam T) ∧
    (∀ T ∈ S.powerset, w T < z → lam T = 0) ∧
    (∀ j ∈ S, ∑ T ∈ S.powerset with j ∈ T, lam T ≤ β)}

theorem card_inter_eq_sum {m : ℕ} (T Q : Finset (Fin m)) :
    ((T ∩ Q).card : ℝ) = ∑ e ∈ Q, if e ∈ T then (1 : ℝ) else 0 := by
  classical
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- Equation (2) of the proof of Lemma 4.6: after the first stage, the remaining items carry a
packing of value `2z/5` for the entitlement `b_i / (2B')`. -/
theorem eq2 {m m' : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β) (z : ℝ)
    (hz : 0 < z) (lam : Finset (Fin m) → ℝ)
    (h1 : ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset, lam T = 1)
    (h2 : ∀ T ∈ (Finset.univ : Finset (Fin m)).powerset, 0 ≤ lam T)
    (h3 : ∀ T ∈ (Finset.univ : Finset (Fin m)).powerset, addVal u T < z → lam T = 0)
    (h4 : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset with j ∈ T, lam T ≤ β)
    (Q1 Q2 : Finset (Fin m)) (hQ : Disjoint Q1 Q2)
    (ι : Fin m' ↪ Fin m) (hrange : ∀ j, j ∉ Q1 ∪ Q2 ↔ ∃ a, ι a = j)
    (hQ2 : ∀ e ∈ Q2, u e < 3 * z / 5)
    (hM1 : ∀ e, e ∉ Q1 ∪ Q2 → u e < 3 * z / 5)
    (hM2 : ∀ e e', e ∉ Q1 ∪ Q2 → e' ∉ Q1 ∪ Q2 → e ≠ e' → u e + u e' < 3 * z / 5)
    (B : ℝ) (hB : 0 < B) (hBle : B ≤ 1 - β * Q1.card - β / 2 * Q2.card) :
    2 * z / 5 ∈ Zset (β / (2 * B)) (addVal (u ∘ ι)) Finset.univ := by
  classical
  set Q := Q1 ∪ Q2 with hQdef
  let pre : Finset (Fin m) → Finset (Fin m') := fun A => Finset.univ.filter (fun a => ι a ∈ A)
  have hpreval : ∀ X : Finset (Fin m), Disjoint X Q → addVal (u ∘ ι) (pre X) = addVal u X := by
    intro X hX
    rw [addVal_map, preimage_map ι X]
    intro j hj
    exact (hrange j).1 (Finset.disjoint_left.1 hX hj)
  let typ2 : Finset (Fin m) → Prop := fun T => Disjoint T Q1 ∧ (T ∩ Q2).card = 1
  let typ3 : Finset (Fin m) → Prop := fun T => Disjoint T Q
  have hsplit : ∀ T, typ3 T → z ≤ addVal u T →
      ∃ C ⊆ T, 2 * z / 5 ≤ addVal u C ∧ 2 * z / 5 ≤ addVal u (T \ C) := by
    intro T hT hzT
    refine split_bundle u hu z hz T hzT (fun e he => hM1 e (Finset.disjoint_left.1 hT he))
      (fun e he e' he' hne => hM2 e e' (Finset.disjoint_left.1 hT he)
        (Finset.disjoint_left.1 hT he') hne)
  let Cf : Finset (Fin m) → Finset (Fin m) := fun T =>
    if h : typ3 T ∧ z ≤ addVal u T then Classical.choose (hsplit T h.1 h.2) else ∅
  have hCf : ∀ T, typ3 T → z ≤ addVal u T → Cf T ⊆ T ∧ 2 * z / 5 ≤ addVal u (Cf T) ∧
      2 * z / 5 ≤ addVal u (T \ Cf T) := by
    intro T h3T hzT
    have := Classical.choose_spec (hsplit T h3T hzT)
    simp only [Cf, dif_pos (And.intro h3T hzT)]
    exact ⟨this.1, this.2.1, this.2.2⟩
  have hCfsub : ∀ T, Cf T ⊆ T := by
    intro T
    by_cases h : typ3 T ∧ z ≤ addVal u T
    · exact (hCf T h.1 h.2).1
    · simp only [Cf, dif_neg h]; exact Finset.empty_subset _
  let g : Finset (Fin m) → Finset (Fin m') → ℝ := fun T A =>
    (if typ2 T ∧ A = pre (T \ Q2) then 1 else 0) + (if typ3 T ∧ A = pre (Cf T) then 1 else 0) +
      (if typ3 T ∧ A = pre (T \ Cf T) then 1 else 0)
  set P := (Finset.univ : Finset (Fin m)).powerset
  set P' := (Finset.univ : Finset (Fin m')).powerset
  let lam' : Finset (Fin m') → ℝ := fun A => ∑ T ∈ P, lam T / (2 * B) * g T A
  set W := ∑ A ∈ P', lam' A with hW
  have hmemP' : ∀ A : Finset (Fin m'), A ∈ P' := fun A => Finset.mem_powerset.2 (Finset.subset_univ _)
  have hg0 : ∀ T A, 0 ≤ g T A := by
    intro T A; simp only [g]; positivity
  -- total weight of the new bundles
  have hsumg : ∀ T, ∑ A ∈ P', g T A =
      (if typ2 T then 1 else 0) + 2 * (if typ3 T then 1 else 0) := by
    intro T
    simp only [g, Finset.sum_add_distrib, ite_and]
    rw [Finset.sum_ite_irrel, Finset.sum_ite_irrel, Finset.sum_ite_irrel]
    simp only [Finset.sum_ite_eq', hmemP', if_true, Finset.sum_const_zero]
    split_ifs <;> ring
  have hW_eq : W = ∑ T ∈ P, lam T / (2 * B) *
      ((if typ2 T then 1 else 0) + 2 * (if typ3 T then 1 else 0)) := by
    rw [hW]
    simp only [lam']
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro T _
    rw [← Finset.mul_sum, hsumg]
  -- pointwise bound for the weight of a bundle
  have hpt : ∀ T, (2 : ℝ) - 2 * (T ∩ Q1).card - (T ∩ Q2).card ≤
      (if typ2 T then 1 else 0) + 2 * (if typ3 T then 1 else 0) := by
    intro T
    by_cases hq1 : Disjoint T Q1
    · have hc1 : (T ∩ Q1).card = 0 := by
        rw [Finset.card_eq_zero]; exact Finset.disjoint_iff_inter_eq_empty.1 hq1
      rcases Nat.lt_or_ge (T ∩ Q2).card 2 with hc | hc
      · rcases (show (T ∩ Q2).card = 0 ∨ (T ∩ Q2).card = 1 by omega) with hc2 | hc2
        · have h3 : typ3 T := by
            simp only [typ3, hQdef, Finset.disjoint_union_right]
            exact ⟨hq1, Finset.disjoint_iff_inter_eq_empty.2 (Finset.card_eq_zero.1 hc2)⟩
          have h2n : ¬ typ2 T := fun h => by simp only [typ2] at h; omega
          rw [if_neg h2n, if_pos h3, hc1, hc2]; norm_num
        · have h2 : typ2 T := ⟨hq1, hc2⟩
          have h3n : ¬ typ3 T := by
            intro h; simp only [typ3, hQdef, Finset.disjoint_union_right] at h
            rw [Finset.disjoint_iff_inter_eq_empty.1 h.2] at hc2; simp at hc2
          rw [if_pos h2, if_neg h3n, hc1, hc2]; norm_num
      · have : (2 : ℝ) ≤ (T ∩ Q2).card := by exact_mod_cast hc
        have : (0 : ℝ) ≤ (if typ2 T then 1 else 0) + 2 * (if typ3 T then 1 else 0) := by
          positivity
        push_cast; linarith [(Nat.cast_nonneg (T ∩ Q1).card : (0 : ℝ) ≤ _)]
    · have hc1 : 1 ≤ (T ∩ Q1).card := by
        rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
        intro h; exact hq1 (Finset.disjoint_iff_inter_eq_empty.2 h)
      have : (1 : ℝ) ≤ (T ∩ Q1).card := by exact_mod_cast hc1
      have : (0 : ℝ) ≤ (if typ2 T then 1 else 0) + 2 * (if typ3 T then 1 else 0) := by positivity
      linarith [(Nat.cast_nonneg (T ∩ Q2).card : (0 : ℝ) ≤ _)]
  -- loads of the removed items
  have hload : ∀ Qx : Finset (Fin m), ∑ T ∈ P, lam T * (T ∩ Qx).card ≤ β * Qx.card := by
    intro Qx
    simp_rw [card_inter_eq_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ e ∈ Qx, ∑ T ∈ P, lam T * (if e ∈ T then (1 : ℝ) else 0)
        = ∑ e ∈ Qx, ∑ T ∈ P with e ∈ T, lam T := by
          apply Finset.sum_congr rfl; intro e _
          rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro T _; split_ifs <;> ring
      _ ≤ ∑ e ∈ Qx, β := Finset.sum_le_sum fun e _ => h4 e (Finset.mem_univ e)
      _ = β * Qx.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hW1 : 1 ≤ W := by
    rw [hW_eq]
    have hlow : ∑ T ∈ P, lam T * (2 - 2 * (T ∩ Q1).card - (T ∩ Q2).card) ≤
        ∑ T ∈ P, lam T * ((if typ2 T then 1 else 0) + 2 * (if typ3 T then 1 else 0)) :=
      Finset.sum_le_sum fun T hT => mul_le_mul_of_nonneg_left (hpt T) (h2 T hT)
    have hexp : ∑ T ∈ P, lam T * (2 - 2 * (T ∩ Q1).card - (T ∩ Q2).card) =
        2 - 2 * ∑ T ∈ P, lam T * (T ∩ Q1).card - ∑ T ∈ P, lam T * (T ∩ Q2).card := by
      have e : ∀ T : Finset (Fin m), lam T * (2 - 2 * ((T ∩ Q1).card : ℝ) - (T ∩ Q2).card) =
          2 * lam T - 2 * (lam T * (T ∩ Q1).card) - lam T * (T ∩ Q2).card := fun T => by ring
      simp_rw [e]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]
      ring
    have hl1 := hload Q1
    have hl2 := hload Q2
    have e : ∑ T ∈ P, lam T / (2 * B) *
        ((if typ2 T then 1 else 0) + 2 * (if typ3 T then 1 else 0)) =
        (∑ T ∈ P, lam T * ((if typ2 T then 1 else 0) + 2 * (if typ3 T then 1 else 0))) /
          (2 * B) := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro T _; ring
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  have hWpos : 0 < W := by linarith
  refine ⟨fun A => lam' A / W, ?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_div, ← hW, div_self hWpos.ne']
  · intro A _
    apply div_nonneg _ hWpos.le
    exact Finset.sum_nonneg fun T hT => mul_nonneg (div_nonneg (h2 T hT) (by positivity)) (hg0 T A)
  · intro A _ hA
    rw [div_eq_zero_iff]; left
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hzT : addVal u T < z
    · rw [h3 T hT hzT]; simp
    push Not at hzT
    have hgz : g T A = 0 := by
      simp only [g]
      have e1 : ¬ (typ2 T ∧ A = pre (T \ Q2)) := by
        rintro ⟨⟨hq1, hc⟩, rfl⟩
        obtain ⟨e, he⟩ := Finset.card_eq_one.1 hc
        have heT : e ∈ T := (Finset.mem_inter.1 (he ▸ Finset.mem_singleton_self e)).1
        have heQ : e ∈ Q2 := (Finset.mem_inter.1 (he ▸ Finset.mem_singleton_self e)).2
        have hTQ : T \ Q2 = T.erase e := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]
          constructor
          · rintro ⟨hx, hxQ⟩; exact ⟨fun h => hxQ (h ▸ heQ), hx⟩
          · rintro ⟨hxe, hx⟩
            refine ⟨hx, fun hxQ => hxe ?_⟩
            have : x ∈ T ∩ Q2 := Finset.mem_inter.2 ⟨hx, hxQ⟩
            rw [he] at this; simpa using this
        have hdisj : Disjoint (T \ Q2) Q := by
          rw [hQdef, Finset.disjoint_union_right]
          exact ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset hq1, Finset.sdiff_disjoint⟩
        rw [hpreval _ hdisj, hTQ] at hA
        have : addVal u (T.erase e) = addVal u T - u e := by
          unfold addVal; rw [← Finset.add_sum_erase T u heT]; ring
        rw [this] at hA
        have := hQ2 e heQ
        linarith
      have e2 : ¬ (typ3 T ∧ A = pre (Cf T)) := by
        rintro ⟨h3T, rfl⟩
        obtain ⟨hsub, hC1, -⟩ := hCf T h3T hzT
        rw [hpreval _ (Finset.disjoint_of_subset_left hsub h3T)] at hA
        linarith
      have e3 : ¬ (typ3 T ∧ A = pre (T \ Cf T)) := by
        rintro ⟨h3T, rfl⟩
        obtain ⟨-, -, hC2⟩ := hCf T h3T hzT
        rw [hpreval _ (Finset.disjoint_of_subset_left Finset.sdiff_subset h3T)] at hA
        linarith
      rw [if_neg e1, if_neg e2, if_neg e3]; ring
    rw [hgz, mul_zero]
  · intro a _
    -- the load of `a` is at most that of `ι a`, scaled by `1 / (2B)`
    have hind : ∀ (X : Finset (Fin m')) (q : Prop) [Decidable q],
        ∑ A ∈ P' with a ∈ A, (if q ∧ A = X then (1 : ℝ) else 0) = if q ∧ a ∈ X then 1 else 0 := by
      intro X q _
      rw [Finset.sum_filter]
      rw [Finset.sum_eq_single X]
      · by_cases hq : q <;> by_cases hX : a ∈ X <;> simp [hq, hX]
      · intro A _ hAX; simp [hAX]
      · intro h; exact absurd (hmemP' X) h
    have hpre : ∀ X, a ∈ pre X ↔ ι a ∈ X := fun X => by simp [pre]
    have hga : ∀ T, ∑ A ∈ P' with a ∈ A, g T A ≤ if ι a ∈ T then 1 else 0 := by
      intro T
      simp only [g, Finset.sum_add_distrib]
      rw [hind, hind, hind]
      simp only [hpre]
      by_cases h3T : typ3 T
      · have h2n : ¬ typ2 T := by
          rintro ⟨-, hc⟩
          simp only [typ3, hQdef, Finset.disjoint_union_right] at h3T
          rw [Finset.disjoint_iff_inter_eq_empty.1 h3T.2] at hc; simp at hc
        by_cases hC : ι a ∈ Cf T
        · have : ι a ∈ T := hCfsub T hC
          simp [h2n, h3T, hC, this]
        · by_cases hT : ι a ∈ T <;> simp [h2n, h3T, hC, hT]
      · by_cases hT : ι a ∈ T
        · by_cases h2T : typ2 T <;> simp [h2T, h3T, hT] <;> split_ifs <;> norm_num
        · have : ι a ∉ T \ Q2 := fun h => hT (Finset.mem_sdiff.1 h).1
          simp [h3T, hT, this]
    have hload' : ∑ A ∈ P' with a ∈ A, lam' A ≤ β / (2 * B) := by
      simp only [lam']
      rw [Finset.sum_comm]
      calc ∑ T ∈ P, ∑ A ∈ P' with a ∈ A, lam T / (2 * B) * g T A
          = ∑ T ∈ P, lam T / (2 * B) * ∑ A ∈ P' with a ∈ A, g T A := by
            apply Finset.sum_congr rfl; intro T _; rw [Finset.mul_sum]
        _ ≤ ∑ T ∈ P, lam T / (2 * B) * (if ι a ∈ T then 1 else 0) :=
            Finset.sum_le_sum fun T hT =>
              mul_le_mul_of_nonneg_left (hga T) (div_nonneg (h2 T hT) (by positivity))
        _ = (∑ T ∈ P with ι a ∈ T, lam T) / (2 * B) := by
            rw [Finset.sum_filter, Finset.sum_div]
            apply Finset.sum_congr rfl; intro T _; split_ifs <;> ring
        _ ≤ β / (2 * B) := div_le_div_of_nonneg_right (h4 _ (Finset.mem_univ _)) (by positivity)
    rw [← Finset.sum_div, div_le_iff₀ hWpos]
    have : β / (2 * B) ≤ β / (2 * B) * W := le_mul_of_one_le_right (by positivity) hW1
    linarith

/-- Indicator vector of a bundle. -/
def ind {m : ℕ} (T : Finset (Fin m)) : Fin m → ℝ := fun j => if j ∈ T then 1 else 0

theorem ind_inj {m : ℕ} {T T' : Finset (Fin m)} (h : ind T = ind T') : T = T' := by
  ext j
  have := congrFun h j
  simp only [ind] at this
  by_cases h1 : j ∈ T <;> by_cases h2 : j ∈ T' <;> simp_all

/-- Linear functionals on `Fin m → ℝ` are given by their coefficients. -/
theorem dual_apply {m : ℕ} (f : StrongDual ℝ (Fin m → ℝ)) (y : Fin m → ℝ) :
    f y = ∑ j, y j * f (fun j' => if j = j' then 1 else 0) := by
  conv_lhs => rw [pi_eq_sum_univ y]
  rw [map_sum]
  simp [map_smul, smul_eq_mul]

/-- Farkas-type alternative: either some convex combination of the bundles of `F` loads every
item of `S` by at most `β`, or there are non-negative item weights `d` on `S` under which every
bundle of `F` weighs more than `β · d(S)`. -/
theorem alternative {m : ℕ} (S : Finset (Fin m)) (F : Finset (Finset (Fin m)))
    (hF : ∀ T ∈ F, T ⊆ S) (β : ℝ) :
    (∃ y ∈ convexHull ℝ (↑(F.image ind) : Set (Fin m → ℝ)), ∀ j ∈ S, y j ≤ β) ∨
    (∃ d : Fin m → ℝ, (∀ j ∈ S, 0 ≤ d j) ∧ ∀ T ∈ F, β * ∑ j ∈ S, d j < ∑ j ∈ T, d j) := by
  classical
  set K := convexHull ℝ (↑(F.image ind) : Set (Fin m → ℝ))
  set C : Set (Fin m → ℝ) := {y | ∀ j ∈ S, y j ≤ β}
  by_cases hdisj : Disjoint K C
  · right
    have hKc : IsCompact K := (F.image ind).finite_toSet.isCompact_convexHull ℝ
    have hKv : Convex ℝ K := convex_convexHull ℝ _
    have hCc : IsClosed C := by
      have : C = ⋂ j ∈ S, {y : Fin m → ℝ | y j ≤ β} := by ext y; simp [C]
      rw [this]
      exact isClosed_biInter fun j _ => isClosed_le (continuous_apply j) continuous_const
    have hCv : Convex ℝ C := by
      intro y hy y' hy' a a' ha ha' haa j hj
      show a * y j + a' * y' j ≤ β
      have e : a * β + a' * β = β := by rw [← add_mul, haa, one_mul]
      linarith [mul_le_mul_of_nonneg_left (hy j hj) ha, mul_le_mul_of_nonneg_left (hy' j hj) ha']
    obtain ⟨f, u, v, hfK, huv, hfC⟩ := geometric_hahn_banach_compact_closed hKv hKc hCv hCc hdisj
    set c : Fin m → ℝ := fun j => f (fun j' => if j = j' then 1 else 0) with hc
    have hf : ∀ y, f y = ∑ j, y j * c j := dual_apply f
    set one : Fin m → ℝ := fun _ => β
    have hone : one ∈ C := fun j _ => le_rfl
    have hfone := hfC one hone
    -- coefficients vanish off `S` and are non-positive on `S`
    have hcS : ∀ j ∈ S, c j ≤ 0 := by
      intro j hj
      by_contra hpos
      push Not at hpos
      set t := (f one - v) / c j + 1
      have ht : 0 ≤ t := by
        have : 0 ≤ (f one - v) / c j := div_nonneg (by linarith) hpos.le
        linarith
      set yt : Fin m → ℝ := fun j' => β - t * (if j = j' then 1 else 0)
      have hyt : yt ∈ C := by
        intro j' _; simp only [yt]; split_ifs <;> nlinarith
      have h1 := hfC yt hyt
      have h2 : f yt = f one - t * c j := by
        rw [hf, hf]
        simp only [yt, one, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
        rw [Finset.sum_boole_mul]; simp
      have h3 : t * c j = f one - v + c j := by
        simp only [t]; field_simp
      linarith
    have hcnS : ∀ j ∉ S, c j = 0 := by
      intro j hj
      by_contra hne
      set t := -(f one - v + 1) / c j
      set yt : Fin m → ℝ := fun j' => β + t * (if j = j' then 1 else 0)
      have hyt : yt ∈ C := by
        intro j' hj'; simp only [yt]
        have : j ≠ j' := fun h => hj (h ▸ hj')
        simp [this]
      have h1 := hfC yt hyt
      have h2 : f yt = f one + t * c j := by
        rw [hf, hf]
        simp only [yt, one, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        rw [Finset.sum_boole_mul]; simp
      have h3 : t * c j = -(f one - v + 1) := by
        simp only [t]; field_simp
      linarith
    have hsumS : ∀ T ⊆ S, ∑ j, ind T j * c j = ∑ j ∈ T, c j := by
      intro T _
      simp only [ind, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    refine ⟨fun j => - c j, fun j hj => by linarith [hcS j hj], fun T hT => ?_⟩
    have hTK : ind T ∈ K := subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem ind hT))
    have h1 := hfK _ hTK
    rw [hf, hsumS T (hF T hT)] at h1
    have h2 : f one = β * ∑ j ∈ S, c j := by
      rw [hf, Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [hcnS j hj, mul_zero])]
    simp only [Finset.sum_neg_distrib, mul_neg]
    linarith
  · left
    rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨y, hyK, hyC⟩ := hdisj
    exact ⟨y, hyK, hyC⟩


theorem anyPrice_mem_Zset {m : ℕ} (w : Finset (Fin m) → ℝ) (hmono : Monotone w) (hnorm : w ∅ = 0)
    (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) : anyPrice β w S ∈ Zset β w S := by
  classical
  have hw0 : ∀ T, 0 ≤ w T := fun T => hnorm ▸ hmono (Finset.empty_subset T)
  have hAne : ∀ p : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1},
      Nonempty {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p.1 j ≤ β} :=
    fun p => ⟨⟨∅, Finset.empty_subset _, by simpa using hβ.le⟩⟩
  have hbddA : ∀ p : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1},
      BddAbove (Set.range fun T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p.1 j ≤ β} =>
        w T.1) := fun p => (Set.finite_range _).bddAbove
  have hbddP : BddBelow (Set.range fun p : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧
      ∑ j ∈ S, p j = 1} => ⨆ T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p.1 j ≤ β}, w T.1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    haveI := hAne p
    exact le_ciSup_of_le (hbddA p) (Classical.arbitrary _) (hw0 _)
  have hzero : (0 : ℝ) ∈ Zset β w S := by
    refine ⟨fun T => if T = ∅ then 1 else 0, ?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_ite_eq']; simp
    · intro T _; dsimp only; split_ifs <;> norm_num
    · intro T _ hT
      have : w ∅ ≤ w T := hmono (Finset.empty_subset T)
      exfalso; linarith
    · intro j _
      rw [Finset.sum_eq_zero]
      · exact hβ.le
      · intro T hT
        simp only [Finset.mem_filter] at hT
        rw [if_neg]; rintro rfl; simp at hT
  have hle_mem : ∀ z z', z ∈ Zset β w S → z' ≤ z → z' ∈ Zset β w S := by
    rintro z z' ⟨lam, h1, h2, h3, h4⟩ hz'
    exact ⟨lam, h1, h2, fun T hT hlt => h3 T hT (lt_of_lt_of_le hlt hz'), h4⟩
  set z := anyPrice β w S with hzdef
  by_cases hz0 : z ≤ 0
  · exact hle_mem 0 z hzero hz0
  push Not at hz0
  set F := S.powerset.filter (fun T => z ≤ w T) with hFdef
  have hFsub : ∀ T ∈ F, T ⊆ S := fun T hT => Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
  have hindinj : Set.InjOn ind (↑F : Set (Finset (Fin m))) :=
    fun T _ T' _ h => ind_inj h
  rcases alternative S F hFsub β with ⟨y, hyK, hyC⟩ | ⟨d, hd0, hdF⟩
  · -- a convex combination of good bundles loads every item by at most `β`
    rw [Finset.mem_convexHull] at hyK
    obtain ⟨μ, hμ0, hμ1, hμc⟩ := hyK
    have hy : ∀ j, y j = ∑ T ∈ F, μ (ind T) * ind T j := by
      intro j
      rw [← hμc, Finset.centerMass, hμ1, inv_one, one_smul, Finset.sum_apply,
        Finset.sum_image hindinj]
      simp
    refine ⟨fun T => if T ∈ F then μ (ind T) else 0, ?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (Finset.filter_subset _ _),
        ← Finset.sum_image hindinj, hμ1]
    · intro T _
      dsimp only
      split_ifs with hT
      · exact hμ0 _ (Finset.mem_image_of_mem ind hT)
      · exact le_rfl
    · intro T hT hlt
      dsimp only
      rw [if_neg]
      intro hTF
      exact absurd (Finset.mem_filter.1 hTF).2 (not_le.2 hlt)
    · intro j hj
      rw [Finset.sum_filter]
      have : ∑ T ∈ S.powerset, (if j ∈ T then (if T ∈ F then μ (ind T) else 0) else 0) =
          ∑ T ∈ S.powerset, (if T ∈ F then μ (ind T) * ind T j else 0) := by
        apply Finset.sum_congr rfl; intro T _
        simp only [ind]
        split_ifs <;> simp
      rw [this, Finset.sum_ite_mem, Finset.inter_eq_right.2 (Finset.filter_subset _ _), ← hy]
      exact hyC j hj
  · -- otherwise a price vector makes every good bundle unaffordable
    exfalso
    have hSne : S.Nonempty := by
      rcases S.eq_empty_or_nonempty with hS | hS
      · exfalso
        have hE : z = 0 := by
          rw [hzdef, hS]
          unfold anyPrice
          haveI : IsEmpty {p : Fin m → ℝ // (∀ j ∈ (∅ : Finset (Fin m)), 0 ≤ p j) ∧
              ∑ j ∈ (∅ : Finset (Fin m)), p j = 1} := ⟨fun q => by simpa using q.2.2⟩
          exact Real.iInf_of_isEmpty _
        linarith
      · exact hS
    obtain ⟨j0, hj0⟩ := hSne
    obtain ⟨p, hp0, hp1, hpF⟩ : ∃ p : Fin m → ℝ, (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1 ∧
        ∀ T ∈ F, β < ∑ j ∈ T, p j := by
      by_cases hFne : F.Nonempty
      · obtain ⟨T0, hT0⟩ := hFne
        have hD0 : 0 ≤ ∑ j ∈ S, d j := Finset.sum_nonneg hd0
        have hTD : ∑ j ∈ T0, d j ≤ ∑ j ∈ S, d j :=
          Finset.sum_le_sum_of_subset_of_nonneg (hFsub T0 hT0) fun j hj _ => hd0 j hj
        have hDpos : 0 < ∑ j ∈ S, d j := by
          rcases hD0.eq_or_lt with h | h
          · have := hdF T0 hT0; rw [← h] at this hTD; linarith
          · exact h
        refine ⟨fun j => d j / ∑ j ∈ S, d j, fun j hj => div_nonneg (hd0 j hj) hD0, ?_, ?_⟩
        · rw [← Finset.sum_div, div_self hDpos.ne']
        · intro T hT
          rw [← Finset.sum_div, lt_div_iff₀ hDpos]
          exact hdF T hT
      · refine ⟨fun j => if j = j0 then 1 else 0, fun j _ => by dsimp only; split_ifs <;> norm_num,
          by simp [hj0], fun T hT => absurd ⟨T, hT⟩ hFne⟩
    have hle : z ≤ ⨆ T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p j ≤ β}, w T.1 := by
      rw [hzdef]; unfold anyPrice
      exact ciInf_le hbddP ⟨p, hp0, hp1⟩
    haveI := hAne ⟨p, hp0, hp1⟩
    obtain ⟨T, hT⟩ := exists_eq_ciSup_of_finite
      (f := fun T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p j ≤ β} => w T.1)
    rw [← hT] at hle
    have hTF : T.1 ∉ F := fun hTF => absurd T.2.2 (not_le.2 (hpF T.1 hTF))
    have : w T.1 < z := by
      by_contra hc
      push Not at hc
      exact hTF (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 T.2.1, hc⟩)
    linarith

/-! ### The strategy of Lemma 4.6 -/

section strat

variable {n m : ℕ}

/-- Steps 1–2 apply: the two most valuable remaining items are worth at least `θ`. -/
def cnd (v : Fin m → ℝ) (θ : ℝ) (g : List (Round n m)) : Prop :=
  θ ≤ rankedValue v (remaining g) 1 + rankedValue v (remaining g) 2

/-- Still in the first stage: steps 1–2 applied at every round so far. -/
def phase1 (v : Fin m → ℝ) (θ : ℝ) (g : List (Round n m)) : Prop :=
  ∀ k ≤ g.length, cnd v θ (g.take k)

/-- Agent `i` won a round of the first stage. -/
def wonP1 (v : Fin m → ℝ) (θ : ℝ) (i : Fin n) (g : List (Round n m)) : Prop :=
  ∃ (k : ℕ) (hk : k < g.length), g[k].winner = i ∧ phase1 v θ (g.take k)

open Classical in
/-- The round `t'` at which the first stage ends. -/
noncomputable def tp (v : Fin m → ℝ) (θ : ℝ) (g : List (Round n m)) : ℕ :=
  if h : ∃ k, k ≤ g.length ∧ ¬ cnd v θ (g.take k) then Nat.find h else g.length

/-- Normalised budgets of agent `i` and of the merged adversary. -/
noncomputable def b2 (b : Fin n → ℝ) (i : Fin n) (h0 : List (Round n m)) : Fin 2 → ℝ :=
  ![budget b h0 i / totalBudget b h0,
    (∑ k ∈ Finset.univ.erase i, budget b h0 k) / totalBudget b h0]

/-- The remaining items, indexed by `Fin`. -/
noncomputable def ιf (h0 : List (Round n m)) : Fin (remaining h0).card ↪ Fin m :=
  ⟨fun a => ((remaining h0).equivFin.symm a).1,
    fun a a' h => (remaining h0).equivFin.symm.injective (Subtype.ext h)⟩

theorem ιf_range (h0 : List (Round n m)) (j : Fin m) :
    j ∈ remaining h0 ↔ ∃ a, ιf h0 a = j := by
  constructor
  · intro hj
    refine ⟨(remaining h0).equivFin ⟨j, hj⟩, ?_⟩
    show (((remaining h0).equivFin.symm ((remaining h0).equivFin ⟨j, hj⟩)) : Fin m) = j
    rw [Equiv.symm_apply_apply]
  · rintro ⟨a, rfl⟩
    exact ((remaining h0).equivFin.symm a).2

open Classical in
/-- The strategy of Lemma 4.7 in the continuation game. -/
noncomputable def σ'f (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (b : Fin n → ℝ) (i : Fin n)
    (h0 : List (Round n m)) : Strategy 2 (remaining h0).card :=
  if hyp : (∀ k, 0 < b2 b i h0 k) ∧ ∑ k, b2 b i h0 k = 1 then
    Classical.choose (AnyPriceShare.Bidding.lemma_4_7 (v ∘ ιf h0) (fun _ => hv _) (b2 b i h0)
      hyp.1 hyp.2 0)
  else fun _ => (0, ∅)

theorem σ'f_spec (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (b : Fin n → ℝ) (i : Fin n)
    (h0 : List (Round n m)) (hyp : (∀ k, 0 < b2 b i h0 k) ∧ ∑ k, b2 b i h0 k = 1) :
    Guarantees (b2 b i h0) (σ'f v hv b i h0) 0 (v ∘ ιf h0)
      (3 / 2 * anyPrice (b2 b i h0 0 / 2) (addVal (v ∘ ιf h0)) Finset.univ) := by
  have := Classical.choose_spec (AnyPriceShare.Bidding.lemma_4_7 (v ∘ ιf h0) (fun _ => hv _)
    (b2 b i h0) hyp.1 hyp.2 0)
  simp only [σ'f, dif_pos hyp]
  exact this

open Classical in
/-- The strategy of Lemma 4.6 (with `θ = 3z/5`). -/
noncomputable def strat46 (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (b : Fin n → ℝ) (i : Fin n)
    (θ : ℝ) : Strategy n m := fun g =>
  if hR : (remaining g).Nonempty then
    if wonP1 v θ i g then (0, {Classical.choose ((remaining g).exists_max_image v hR)})
    else if phase1 v θ g then
      if θ ≤ rankedValue v (remaining g) 1 then
        (budget b g i, {Classical.choose ((remaining g).exists_max_image v hR)})
      else if h2 : ((remaining g).erase
          (Classical.choose ((remaining g).exists_max_image v hR))).Nonempty then
        (budget b g i / 2, {Classical.choose ((remaining g).exists_max_image v hR),
          Classical.choose (((remaining g).erase
            (Classical.choose ((remaining g).exists_max_image v hR))).exists_max_image v h2)})
      else (0, {Classical.choose ((remaining g).exists_max_image v hR)})
    else if (∀ k, 0 < b2 b i (g.take (tp v θ g)) k) ∧ ∑ k, b2 b i (g.take (tp v θ g)) k = 1 then
      contStrat i (ιf (g.take (tp v θ g))) (totalBudget b (g.take (tp v θ g)))
        (σ'f v hv b i (g.take (tp v θ g))) (g.drop (tp v θ g))
    else (budget b g i / (remaining g).card,
      {Classical.choose ((remaining g).exists_max_image v hR)})
  else (0, ∅)

/-! #### Prefix stability -/

theorem take_take_of_le {α : Type*} (l : List α) {j k : ℕ} (h : j ≤ k) :
    (l.take k).take j = l.take j := by
  rw [List.take_take, min_eq_left h]

theorem wonP1_of_take (v : Fin m → ℝ) (θ : ℝ) (i : Fin n) (h : List (Round n m)) (k : ℕ)
    (hw : wonP1 v θ i (h.take k)) : wonP1 v θ i h := by
  obtain ⟨j, hj, hwin, hph⟩ := hw
  have hjk : j < k := lt_of_lt_of_le hj (by simp)
  have hjh : j < h.length := lt_of_lt_of_le hj (by simp)
  refine ⟨j, hjh, ?_, ?_⟩
  · simpa [List.getElem_take] using hwin
  · rwa [take_take_of_le h hjk.le] at hph

theorem not_phase1_iff (v : Fin m → ℝ) (θ : ℝ) (g : List (Round n m)) :
    ¬ phase1 v θ g ↔ ∃ k, k ≤ g.length ∧ ¬ cnd v θ (g.take k) := by
  simp only [phase1, not_forall, exists_prop]

theorem tp_spec (v : Fin m → ℝ) (θ : ℝ) (g : List (Round n m)) (hg : ¬ phase1 v θ g) :
    tp v θ g ≤ g.length ∧ ¬ cnd v θ (g.take (tp v θ g)) ∧
      ∀ k < tp v θ g, cnd v θ (g.take k) := by
  classical
  have hex := (not_phase1_iff v θ g).1 hg
  have e : tp v θ g = Nat.find hex := by simp only [tp, dif_pos hex]
  rw [e]
  refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk => ?_⟩
  have := Nat.find_min hex hk
  push Not at this
  by_contra hc
  exact absurd (this (by have := (Nat.find_spec hex).1; omega)) hc

theorem tp_take (v : Fin m → ℝ) (θ : ℝ) (h : List (Round n m)) (hh : ¬ phase1 v θ h) (k : ℕ)
    (hk : tp v θ h ≤ k) (hkl : k ≤ h.length) :
    ¬ phase1 v θ (h.take k) ∧ tp v θ (h.take k) = tp v θ h := by
  obtain ⟨t1, t2, t3⟩ := tp_spec v θ h hh
  have hlen : (h.take k).length = k := by simp; omega
  have hn : ¬ phase1 v θ (h.take k) := by
    rw [not_phase1_iff]
    exact ⟨tp v θ h, by omega, by rwa [take_take_of_le h hk]⟩
  refine ⟨hn, ?_⟩
  obtain ⟨s1, s2, s3⟩ := tp_spec v θ (h.take k) hn
  rw [hlen] at s1
  apply le_antisymm
  · by_contra hc
    push Not at hc
    exact t2 (by have := s3 _ hc; rwa [take_take_of_le h hk] at this)
  · by_contra hc
    push Not at hc
    exact s2 (by have := t3 _ hc; rwa [take_take_of_le h s1])

theorem validPlay_take (b : Fin n → ℝ) (h : List (Round n m)) (hp : ValidPlay b h) (t : ℕ) :
    ValidPlay b (h.take t) := by
  intro k hk
  simp only [List.length_take] at hk
  have hk' : k < h.length := by omega
  have := hp k hk'
  simp only [List.get_eq_getElem] at this ⊢
  rw [take_take_of_le h (by omega : k ≤ t)]
  simpa [List.getElem_take] using this

end strat

section legal

variable {n m : ℕ}

theorem drop_take' {α : Type*} (l : List α) (t k : ℕ) : (l.take (t + k)).drop t = (l.drop t).take k := by
  rw [List.drop_take]; congr 1; omega

theorem B_pos_of_hyp (b : Fin n → ℝ) (i : Fin n) (h0 : List (Round n m))
    (hnn : ∀ k, 0 ≤ budget b h0 k) (hyp : (∀ k, 0 < b2 b i h0 k) ∧ ∑ k, b2 b i h0 k = 1) :
    0 < totalBudget b h0 := by
  have h0' := hyp.1 0
  simp only [b2, Matrix.cons_val_zero] at h0'
  have hB0 : 0 ≤ totalBudget b h0 := Finset.sum_nonneg fun k _ => hnn k
  rcases hB0.eq_or_lt with h | h
  · rw [← h, div_zero] at h0'; exact absurd h0' (lt_irrefl 0)
  · exact h

/-- In the second stage, the rounds after `t'` follow the continuation strategy. -/
theorem phase2_follow (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (b : Fin n → ℝ) (i : Fin n) (θ : ℝ)
    (h : List (Round n m)) (hp : ValidPlay b h) (hf : FollowedBy (strat46 v hv b i θ) i h)
    (hw : ¬ wonP1 v θ i h) (hph : ¬ phase1 v θ h)
    (hyp : (∀ k, 0 < b2 b i (h.take (tp v θ h)) k) ∧ ∑ k, b2 b i (h.take (tp v θ h)) k = 1) :
    ∀ (k : ℕ) (hk : k < (h.drop (tp v θ h)).length),
      (h.drop (tp v θ h))[k].bids i = (contStrat i (ιf (h.take (tp v θ h)))
        (totalBudget b (h.take (tp v θ h))) (σ'f v hv b i (h.take (tp v θ h)))
        ((h.drop (tp v θ h)).take k)).1 ∧
      ((h.drop (tp v θ h))[k].winner = i → (h.drop (tp v θ h))[k].taken =
        (contStrat i (ιf (h.take (tp v θ h))) (totalBudget b (h.take (tp v θ h)))
        (σ'f v hv b i (h.take (tp v θ h))) ((h.drop (tp v θ h)).take k)).2) := by
  classical
  intro k hk
  set t := tp v θ h with ht
  have htl : t ≤ h.length := (tp_spec v θ h hph).1
  simp only [List.length_drop] at hk
  have hidx : t + k < h.length := by omega
  obtain ⟨hb1, hb2'⟩ := hf (t + k) hidx
  simp only [List.get_eq_getElem] at hb1 hb2'
  set g := h.take (t + k) with hg
  have hvr := hp (t + k) hidx
  simp only [List.get_eq_getElem] at hvr
  have hR : (remaining g).Nonempty := by
    obtain ⟨j, hj⟩ := hvr.2.2.1; exact ⟨j, hvr.2.2.2.1 hj⟩
  have hwg : ¬ wonP1 v θ i g := fun hh => hw (wonP1_of_take v θ i h _ hh)
  obtain ⟨hphg, htpg⟩ := tp_take v θ h hph (t + k) (by omega) hidx.le
  have hg0 : g.take (tp v θ g) = h.take t := by rw [htpg, hg, take_take_of_le h (by omega)]
  have hgd : g.drop (tp v θ g) = (h.drop t).take k := by rw [htpg, hg, drop_take']
  have hσ : strat46 v hv b i θ g = contStrat i (ιf (h.take t)) (totalBudget b (h.take t))
      (σ'f v hv b i (h.take t)) ((h.drop t).take k) := by
    have hyp' : (∀ k, 0 < b2 b i (g.take (tp v θ g)) k) ∧
        ∑ k, b2 b i (g.take (tp v θ g)) k = 1 := by rw [hg0]; exact hyp
    unfold strat46
    rw [dif_pos hR, if_neg hwg, if_neg hphg, if_pos hyp']
    rw [hg0, hgd]
  have hget : (h.drop t)[k] = h[t + k] := by simp [List.getElem_drop]
  rw [hget, ← hσ]
  exact ⟨hb1, hb2'⟩

theorem strat46_legal (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (b : Fin n → ℝ)
    (hb0 : ∀ k, 0 ≤ b k) (i : Fin n) (θ : ℝ) (h : List (Round n m)) (hp : ValidPlay b h)
    (hf : FollowedBy (strat46 v hv b i θ) i h) (hne : remaining h ≠ ∅) :
    LegalMove b h i (strat46 v hv b i θ h) := by
  classical
  have hR : (remaining h).Nonempty := Finset.nonempty_iff_ne_empty.2 hne
  have hbud := budget_nonneg b hb0 h hp
  obtain ⟨hj1R, -⟩ := Classical.choose_spec ((remaining h).exists_max_image v hR)
  set j1 := Classical.choose ((remaining h).exists_max_image v hR) with hj1
  have hsingle : ∀ x, 0 ≤ x → x ≤ budget b h i → LegalMove b h i (x, {j1}) :=
    fun x hx0 hx1 => ⟨hx0, hx1, Finset.singleton_nonempty _,
      Finset.singleton_subset_iff.2 hj1R, by simpa using hx1⟩
  unfold strat46
  rw [dif_pos hR]
  split_ifs with hw hph hx h2 hyp
  · exact hsingle 0 le_rfl (hbud i)
  · exact hsingle _ (hbud i) le_rfl
  · obtain ⟨hj2R, -⟩ := Classical.choose_spec (((remaining h).erase j1).exists_max_image v h2)
    have hne2 : j1 ≠ Classical.choose (((remaining h).erase j1).exists_max_image v h2) :=
      fun he => by rw [← he] at hj2R; simp at hj2R
    refine ⟨by have := hbud i; positivity, by linarith [hbud i], Finset.insert_nonempty _ _,
      Finset.insert_subset hj1R (Finset.singleton_subset_iff.2 (Finset.mem_of_mem_erase hj2R)), ?_⟩
    rw [Finset.card_pair hne2]; push_cast; linarith
  · exact hsingle 0 le_rfl (hbud i)
  · -- the continuation strategy of Lemma 4.7
    set t := tp v θ h with ht
    have hh : h.take t ++ h.drop t = h := List.take_append_drop t h
    have hp0 := validPlay_take b h hp t
    have hnn0 := budget_nonneg b hb0 _ hp0
    have hBpos := B_pos_of_hyp b i (h.take t) hnn0 hyp
    have hT := transfer b hb0 i (h.take t) hp0 (ιf (h.take t)) (ιf_range (h.take t))
      (totalBudget b (h.take t)) hBpos (b2 b i (h.take t)) (by simp [b2]) (by simp [b2])
      (σ'f v hv b i (h.take t)) v hv _ (σ'f_spec v hv b i (h.take t) hyp) (h.drop t)
      (by rw [hh]; exact hp) (phase2_follow v hv b i θ h hp hf hw hph hyp)
    have := hT.1 (by rw [hh]; exact hne)
    rw [hh] at this
    exact this
  · have hc : (0 : ℝ) < (remaining h).card := by exact_mod_cast Finset.card_pos.2 hR
    have hc1 : (1 : ℝ) ≤ (remaining h).card := by exact_mod_cast Finset.card_pos.2 hR
    refine hsingle _ (div_nonneg (hbud i) hc.le) ?_
    rw [div_le_iff₀ hc]
    nlinarith [hbud i]

end legal

section value

variable {n m : ℕ}

theorem list_sum_take {β : Type*} (h : List β) (f : β → ℝ) (t : ℕ) (ht : t ≤ h.length) :
    ((h.take t).map f).sum = ∑ k ∈ Finset.range t, if hk : k < h.length then f h[k] else 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [take_succ' h t (by omega), List.map_append, List.sum_append, ih (by omega),
      Finset.sum_range_succ, dif_pos (by omega : t < h.length)]
    simp

theorem mem_remaining_take (h : List (Round n m)) (t : ℕ) (j : Fin m) :
    j ∈ remaining (h.take t) ↔ ∀ (k : ℕ) (hk : k < h.length), k < t → j ∉ h[k].taken := by
  simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro H k hk hkt hj
    exact H h[k] (List.mem_iff_getElem.2 ⟨k, by simp; omega, by simp [List.getElem_take]⟩) hj
  · intro H r hr hj
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    simp only [List.length_take] at hk
    exact H k (by omega) (by omega) (by simpa [List.getElem_take] using hj)

theorem taken_disjoint (b : Fin n → ℝ) (h : List (Round n m)) (hp : ValidPlay b h) (k k' : ℕ)
    (hk : k < h.length) (hk' : k' < h.length) (hkk : k < k') (j : Fin m) (hj : j ∈ h[k].taken) :
    j ∉ h[k'].taken := by
  intro hj'
  have hv := hp k' hk'
  simp only [List.get_eq_getElem] at hv
  have := (mem_remaining_take h k' j).1 (hv.2.2.2.1 hj') k hk hkk
  exact this hj

theorem pair_le (u : Fin m → ℝ) (R : Finset (Fin m)) (e e' : Fin m) (he : e ∈ R) (he' : e' ∈ R)
    (hne : e ≠ e') : u e + u e' ≤ rankedValue u R 1 + rankedValue u R 2 := by
  classical
  obtain ⟨j1, hj1, hmax⟩ := R.exists_max_image u ⟨e, he⟩
  have h1 := rankedValue_one u R j1 hj1 hmax
  have hR2 : rankedValue u R 2 = rankedValue u (R.erase j1) 1 :=
    rankedValue_succ u R j1 hj1 hmax 1 le_rfl
  have hle : ∀ x ∈ R.erase j1, u x ≤ rankedValue u R 2 := by
    intro x hx
    obtain ⟨j2, hj2, hmax2⟩ := (R.erase j1).exists_max_image u ⟨x, hx⟩
    rw [hR2, rankedValue_one u _ j2 hj2 hmax2]
    exact hmax2 x hx
  by_cases h1e : e = j1
  · subst h1e
    have := hle e' (Finset.mem_erase.2 ⟨hne.symm, he'⟩)
    linarith
  · by_cases h1e' : e' = j1
    · subst h1e'
      have := hle e (Finset.mem_erase.2 ⟨hne, he⟩)
      linarith
    · have := hle e' (Finset.mem_erase.2 ⟨h1e', he'⟩)
      have := hmax e he
      linarith

theorem budget_take_of_not_won (b : Fin n → ℝ) (i : Fin n) (h : List (Round n m)) (t : ℕ)
    (ht : t ≤ h.length) (hw : ∀ (k : ℕ) (hk : k < h.length), k < t → h[k].winner ≠ i) :
    budget b (h.take t) i = b i := by
  induction t with
  | zero => simp [budget]
  | succ t ih =>
    rw [take_succ' h t (by omega), budget_snoc, ih (by omega) (fun k hk hkt => hw k hk (by omega)),
      if_neg (hw t (by omega) (by omega)), sub_zero]

end value

section valueW

variable {n m : ℕ}

theorem subset_wonBy (i : Fin n) (h : List (Round n m)) (k : ℕ) (hk : k < h.length)
    (hw : h[k].winner = i) : h[k].taken ⊆ wonBy i h := by
  intro j hj
  simp only [wonBy, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨h[k], List.getElem_mem hk, hw, hj⟩

theorem value_W (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (b : Fin n → ℝ) (i : Fin n) (θ : ℝ)
    (hθ : 0 < θ) (h : List (Round n m)) (hp : ValidPlay b h)
    (hf : FollowedBy (strat46 v hv b i θ) i h) (hW : wonP1 v θ i h) :
    θ ≤ addVal v (wonBy i h) := by
  classical
  have hex : ∃ k, ∃ (hk : k < h.length), h[k].winner = i ∧ phase1 v θ (h.take k) := hW
  obtain ⟨k0, ⟨hk0, hwin, hph⟩, hmin⟩ : ∃ k0, (∃ (hk : k0 < h.length), h[k0].winner = i ∧
      phase1 v θ (h.take k0)) ∧ ∀ j < k0, ¬ ∃ (hk : j < h.length), h[j].winner = i ∧
      phase1 v θ (h.take j) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  set g := h.take k0 with hg
  have hglen : g.length = k0 := by simp [hg]; omega
  have hwg : ¬ wonP1 v θ i g := by
    rintro ⟨j, hj, hjw, hjph⟩
    rw [hglen] at hj
    have : ∃ (hk : j < h.length), h[j].winner = i ∧ phase1 v θ (h.take j) := by
      refine ⟨by omega, ?_, ?_⟩
      · simpa [hg, List.getElem_take] using hjw
      · rwa [hg, take_take_of_le h hj.le] at hjph
    exact hmin j hj this
  have hvr := hp k0 hk0
  simp only [List.get_eq_getElem] at hvr
  have hR : (remaining g).Nonempty := by
    obtain ⟨j, hj⟩ := hvr.2.2.1; exact ⟨j, hvr.2.2.2.1 hj⟩
  have hcnd : cnd v θ g := by
    have := hph g.length le_rfl; rwa [List.take_length] at this
  obtain ⟨hj1R, hj1max⟩ := Classical.choose_spec ((remaining g).exists_max_image v hR)
  set j1 := Classical.choose ((remaining g).exists_max_image v hR) with hj1
  have hx : rankedValue v (remaining g) 1 = v j1 := rankedValue_one v _ j1 hj1R hj1max
  have htk := (hf k0 hk0).2
  simp only [List.get_eq_getElem] at htk
  have htaken := htk hwin
  have hsub := subset_wonBy i h k0 hk0 hwin
  have hmono : addVal v (h[k0].taken) ≤ addVal v (wonBy i h) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hv j
  by_cases hrule : θ ≤ rankedValue v (remaining g) 1
  · have hσ : strat46 v hv b i θ g = (budget b g i, {j1}) := by
      unfold strat46; rw [dif_pos hR, if_neg hwg, if_pos hph, if_pos hrule]
    rw [hσ] at htaken
    rw [htaken] at hmono
    simp only [addVal, Finset.sum_singleton] at hmono
    unfold addVal; linarith
  · by_cases h2 : ((remaining g).erase j1).Nonempty
    · obtain ⟨hj2R, hj2max⟩ := Classical.choose_spec (((remaining g).erase j1).exists_max_image v h2)
      set j2 := Classical.choose (((remaining g).erase j1).exists_max_image v h2) with hj2
      have hne : j1 ≠ j2 := fun he => by rw [he] at hj2R; simp at hj2R
      have hy : rankedValue v (remaining g) 2 = v j2 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, rankedValue_succ v _ j1 hj1R hj1max 1 le_rfl,
          rankedValue_one v _ j2 hj2R hj2max]
      have hσ : strat46 v hv b i θ g = (budget b g i / 2, {j1, j2}) := by
        unfold strat46; rw [dif_pos hR, if_neg hwg, if_pos hph, if_neg hrule, dif_pos h2]
      rw [hσ] at htaken
      rw [htaken] at hmono
      simp only [addVal, Finset.sum_pair hne] at hmono
      unfold cnd at hcnd
      unfold addVal; linarith
    · exfalso
      have hcard : (remaining g).card < 2 := by
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := Finset.card_erase_of_mem hj1R
        rw [h2, Finset.card_empty] at this
        omega
      have hy : rankedValue v (remaining g) 2 = 0 := rankedValue_of_card_lt v _ 2 hcard
      unfold cnd at hcnd
      rw [hy, add_zero] at hcnd
      exact hrule hcnd

end valueW

section stage1

variable {n m : ℕ}

theorem not_won_before (v : Fin m → ℝ) (θ : ℝ) (i : Fin n) (h : List (Round n m))
    (hw : ¬ wonP1 v θ i h) (hph : ¬ phase1 v θ h) :
    ∀ (k : ℕ) (hk : k < h.length), k < tp v θ h → h[k].winner ≠ i := by
  intro k hk hkt hwin
  apply hw
  refine ⟨k, hk, hwin, fun j hj => ?_⟩
  have hjk : j ≤ k := by simp at hj; omega
  rw [take_take_of_le h hjk]
  exact (tp_spec v θ h hph).2.2 j (by omega)

theorem bid_stage1 (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (b : Fin n → ℝ) (i : Fin n) (θ : ℝ)
    (h : List (Round n m)) (hp : ValidPlay b h) (hf : FollowedBy (strat46 v hv b i θ) i h)
    (hw : ¬ wonP1 v θ i h) (hph : ¬ phase1 v θ h) (k : ℕ) (hk : k < h.length)
    (hkt : k < tp v θ h) :
    h[k].bids i = if θ ≤ rankedValue v (remaining (h.take k)) 1 then b i else b i / 2 := by
  classical
  set g := h.take k with hg
  have hvr := hp k hk
  simp only [List.get_eq_getElem] at hvr
  have hR : (remaining g).Nonempty := by
    obtain ⟨j, hj⟩ := hvr.2.2.1; exact ⟨j, hvr.2.2.2.1 hj⟩
  have hwg : ¬ wonP1 v θ i g := fun hh => hw (wonP1_of_take v θ i h _ hh)
  have hphg : phase1 v θ g := by
    intro j hj
    have hjk : j ≤ k := by simp [hg] at hj; omega
    rw [hg, take_take_of_le h hjk]
    exact (tp_spec v θ h hph).2.2 j (by omega)
  have hcnd : cnd v θ g := by have := hphg g.length le_rfl; rwa [List.take_length] at this
  have hbud : budget b g i = b i :=
    budget_take_of_not_won b i h k hk.le (fun k' hk' hkk => not_won_before v θ i h hw hph k' hk'
      (by omega))
  have hb1 := (hf k hk).1
  simp only [List.get_eq_getElem] at hb1
  rw [hb1]
  obtain ⟨hj1R, hj1max⟩ := Classical.choose_spec ((remaining g).exists_max_image v hR)
  set j1 := Classical.choose ((remaining g).exists_max_image v hR) with hj1
  by_cases hrule : θ ≤ rankedValue v (remaining g) 1
  · rw [if_pos hrule]
    unfold strat46; rw [dif_pos hR, if_neg hwg, if_pos hphg, if_pos hrule]; exact hbud
  · rw [if_neg hrule]
    by_cases h2 : ((remaining g).erase j1).Nonempty
    · unfold strat46; rw [dif_pos hR, if_neg hwg, if_pos hphg, if_neg hrule, dif_pos h2]
      simp only; rw [hbud]
    · exfalso
      have hcard : (remaining g).card < 2 := by
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := Finset.card_erase_of_mem hj1R
        rw [h2, Finset.card_empty] at this
        omega
      have hy : rankedValue v (remaining g) 2 = 0 := rankedValue_of_card_lt v _ 2 hcard
      unfold cnd at hcnd
      rw [hy, add_zero] at hcnd
      exact hrule hcnd

/-- First-stage accounting (proof of Lemma 4.6): the items consumed by the adversary under
steps 1 and 2, and the remaining total budget. -/
theorem stage1 (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (b : Fin n → ℝ) (hb : ∀ k, 0 < b k)
    (hsum : ∑ k, b k = 1) (i : Fin n) (θ : ℝ)
    (h : List (Round n m)) (hp : ValidPlay b h) (hf : FollowedBy (strat46 v hv b i θ) i h)
    (hw : ¬ wonP1 v θ i h) (hph : ¬ phase1 v θ h) :
    ∃ Q1 Q2 : Finset (Fin m), Disjoint Q1 Q2 ∧
      (∀ j, j ∉ Q1 ∪ Q2 ↔ j ∈ remaining (h.take (tp v θ h))) ∧
      (∀ e ∈ Q2, v e < θ) ∧
      totalBudget b (h.take (tp v θ h)) ≤ 1 - b i * Q1.card - b i / 2 * Q2.card := by
  classical
  set t := tp v θ h with ht
  set L := h.length
  have htL : t ≤ L := (tp_spec v θ h hph).1
  let tk : ℕ → Finset (Fin m) := fun k => if hk : k < L then h[k].taken else ∅
  let r1 : ℕ → Prop := fun k => θ ≤ rankedValue v (remaining (h.take k)) 1
  let Q1 := ((Finset.range t).filter r1).biUnion tk
  let Q2 := ((Finset.range t).filter (fun k => ¬ r1 k)).biUnion tk
  have hmemQ : ∀ j, j ∈ Q1 ∪ Q2 ↔ ∃ k < t, j ∈ tk k := by
    intro j
    simp only [Q1, Q2, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨k, ⟨hk, -⟩, hj⟩ | ⟨k, ⟨hk, -⟩, hj⟩) <;> exact ⟨k, hk, hj⟩
    · rintro ⟨k, hk, hj⟩
      by_cases hr : r1 k
      · exact Or.inl ⟨k, ⟨hk, hr⟩, hj⟩
      · exact Or.inr ⟨k, ⟨hk, hr⟩, hj⟩
  refine ⟨Q1, Q2, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Q1, Q2, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range] at hj1 hj2
    obtain ⟨k, ⟨hk, hr⟩, hjk⟩ := hj1
    obtain ⟨k', ⟨hk', hr'⟩, hjk'⟩ := hj2
    have hkL : k < L := by by_contra hc; simp [tk, hc] at hjk
    have hk'L : k' < L := by by_contra hc; simp [tk, hc] at hjk'
    simp only [tk, dif_pos hkL, dif_pos hk'L] at hjk hjk'
    rcases lt_trichotomy k k' with hlt | heq | hgt
    · exact taken_disjoint b h hp k k' hkL hk'L hlt j hjk hjk'
    · subst heq; exact hr' hr
    · exact taken_disjoint b h hp k' k hk'L hkL hgt j hjk' hjk
  · intro j
    rw [hmemQ, mem_remaining_take]
    constructor
    · intro H k hk hkt hj
      exact H ⟨k, hkt, by show j ∈ (if hk : k < L then h[k].taken else ∅); rw [dif_pos hk]; exact hj⟩
    · rintro H ⟨k, hkt, hj⟩
      have hkL : k < L := by by_contra hc; simp [tk, hc] at hj
      simp only [tk, dif_pos hkL] at hj
      exact H k hkL hkt hj
  · intro e he
    simp only [Q2, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range] at he
    obtain ⟨k, ⟨hk, hr⟩, hek⟩ := he
    have hkL : k < L := by by_contra hc; simp [tk, hc] at hek
    simp only [tk, dif_pos hkL] at hek
    have hvr := hp k hkL
    simp only [List.get_eq_getElem] at hvr
    have heR := hvr.2.2.2.1 hek
    obtain ⟨j1, hj1, hmax⟩ := (remaining (h.take k)).exists_max_image v ⟨e, heR⟩
    have := rankedValue_one v _ j1 hj1 hmax
    have := hmax e heR
    simp only [r1, not_le] at hr
    linarith
  · -- budget accounting
    have hpaid := total_paid b (h.take t)
    rw [Finset.sum_sub_distrib, hsum] at hpaid
    rw [list_sum_take h _ t htL] at hpaid
    have hround : ∀ k ∈ Finset.range t,
        ((tk k).card : ℝ) * (if r1 k then b i else b i / 2) ≤
        (if hk : k < L then (h[k].taken.card : ℝ) * h[k].bids h[k].winner else 0) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hkL : k < L := by omega
      simp only [tk, dif_pos hkL]
      have hbid := bid_stage1 v hv b i θ h hp hf hw hph k hkL hk
      have hwin := (hp k hkL).2.1 i
      simp only [List.get_eq_getElem] at hwin
      rw [← hbid]
      exact mul_le_mul_of_nonneg_left hwin (Nat.cast_nonneg _)
    have hsumle := Finset.sum_le_sum hround
    have hsplit : ∑ k ∈ Finset.range t, ((tk k).card : ℝ) * (if r1 k then b i else b i / 2) =
        b i * ∑ k ∈ (Finset.range t).filter r1, ((tk k).card : ℝ) +
        b i / 2 * ∑ k ∈ (Finset.range t).filter (fun k => ¬ r1 k), ((tk k).card : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; split_ifs <;> ring
    have hQ1 : (Q1.card : ℝ) ≤ ∑ k ∈ (Finset.range t).filter r1, ((tk k).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have hQ2 : (Q2.card : ℝ) ≤ ∑ k ∈ (Finset.range t).filter (fun k => ¬ r1 k),
        ((tk k).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have hbi := (hb i).le
    have e1 := mul_le_mul_of_nonneg_left hQ1 hbi
    have e2 := mul_le_mul_of_nonneg_left hQ2 (by linarith : 0 ≤ b i / 2)
    unfold totalBudget
    linarith

end stage1

section degenerate

variable {n m : ℕ}

theorem degenerate_wins (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (b : Fin n → ℝ)
    (hb0 : ∀ k, 0 ≤ b k) (i : Fin n) (θ : ℝ)
    (h : List (Round n m)) (hp : ValidPlay b h) (hf : FollowedBy (strat46 v hv b i θ) i h)
    (hw : ¬ wonP1 v θ i h) (hph : ¬ phase1 v θ h)
    (hnhyp : ¬ ((∀ k, 0 < b2 b i (h.take (tp v θ h)) k) ∧
      ∑ k, b2 b i (h.take (tp v θ h)) k = 1))
    (hA : ∀ a, a ≠ i → budget b (h.take (tp v θ h)) a = 0)
    (hbi : 0 < budget b (h.take (tp v θ h)) i) (hdone : remaining h = ∅) :
    remaining (h.take (tp v θ h)) ⊆ wonBy i h := by
  classical
  set t := tp v θ h with ht
  set L := h.length with hL
  have htL : t ≤ L := (tp_spec v θ h hph).1
  -- invariant along the second stage
  have inv : ∀ d, t + d ≤ L →
      (∀ a, a ≠ i → budget b (h.take (t + d)) a = 0) ∧
      (0 < budget b (h.take (t + d)) i ∨ remaining (h.take (t + d)) = ∅) ∧
      (∀ (k : ℕ) (hk : k < L), t ≤ k → k < t + d → h[k].winner = i) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨by simpa using hA, Or.inl (by simpa using hbi), fun k _ h1 h2 => by omega⟩
    | succ d ih =>
      intro hd
      obtain ⟨I1, I2, I3⟩ := ih (by omega)
      have hk : t + d < L := by omega
      set g := h.take (t + d) with hg
      have hvr := hp (t + d) hk
      simp only [List.get_eq_getElem] at hvr
      have hR : (remaining g).Nonempty := by
        obtain ⟨j, hj⟩ := hvr.2.2.1; exact ⟨j, hvr.2.2.2.1 hj⟩
      have hbpos : 0 < budget b g i := by
        rcases I2 with h1 | h1
        · exact h1
        · exact absurd h1 (Finset.nonempty_iff_ne_empty.1 hR)
      have hwg : ¬ wonP1 v θ i g := fun hh => hw (wonP1_of_take v θ i h _ hh)
      obtain ⟨hphg, htpg⟩ := tp_take v θ h hph (t + d) (by omega) hk.le
      have hg0 : g.take (tp v θ g) = h.take t := by rw [htpg, hg, take_take_of_le h (by omega)]
      have hnhyp' : ¬ ((∀ k, 0 < b2 b i (g.take (tp v θ g)) k) ∧
          ∑ k, b2 b i (g.take (tp v θ g)) k = 1) := by rw [hg0]; exact hnhyp
      obtain ⟨hj1R, -⟩ := Classical.choose_spec ((remaining g).exists_max_image v hR)
      set j1 := Classical.choose ((remaining g).exists_max_image v hR) with hj1
      have hσ : strat46 v hv b i θ g = (budget b g i / (remaining g).card, {j1}) := by
        unfold strat46; rw [dif_pos hR, if_neg hwg, if_neg hphg, if_neg hnhyp']
      obtain ⟨hb1, hb2'⟩ := hf (t + d) hk
      simp only [List.get_eq_getElem] at hb1 hb2'
      rw [hσ] at hb1 hb2'
      have hcard : (0 : ℝ) < (remaining g).card := by exact_mod_cast Finset.card_pos.2 hR
      have hbidpos : 0 < h[t + d].bids i := by rw [hb1]; positivity
      -- agent `i` wins: the others cannot bid anything positive
      have hwin : h[t + d].winner = i := by
        by_contra hc
        have h1 := hvr.2.1 i
        have h2 := (hvr.1 h[t + d].winner).2
        rw [I1 _ hc] at h2
        linarith
      have htk : h[t + d].taken = {j1} := hb2' hwin
      have hnext : h.take (t + (d + 1)) = g ++ [h[t + d]] := by
        rw [show t + (d + 1) = t + d + 1 by omega, take_succ' h (t + d) hk]
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        rw [hnext, budget_snoc, I1 a ha, if_neg (by rw [hwin]; exact Ne.symm ha)]
        simp
      · rw [hnext]
        by_cases h2 : 2 ≤ (remaining g).card
        · left
          rw [budget_snoc, if_pos hwin, htk, hb1]
          simp only [Finset.card_singleton, Nat.cast_one, one_mul]
          have hc2 : (2 : ℝ) ≤ (remaining g).card := by exact_mod_cast h2
          have : budget b g i / (remaining g).card ≤ budget b g i / 2 :=
            div_le_div_of_nonneg_left hbpos.le (by norm_num) hc2
          linarith
        · right
          rw [remaining_snoc, htk]
          have hc1 : (remaining g).card = 1 := by
            have := Finset.card_pos.2 hR; omega
          obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc1
          rw [ha] at hj1R ⊢
          rw [Finset.mem_singleton] at hj1R
          rw [hj1R]; simp
      · intro k hk' h1 h2
        rcases Nat.lt_succ_iff_lt_or_eq.1 (by omega : k < t + d + 1) with h3 | h3
        · exact I3 k hk' h1 h3
        · subst h3; exact hwin
  obtain ⟨-, -, I3⟩ := inv (L - t) (by omega)
  intro j hj
  have hjgone : j ∉ remaining (h.take L) := by rw [hL, List.take_length, hdone]; simp
  rw [mem_remaining_take] at hjgone
  push Not at hjgone
  obtain ⟨k, hk, -, hjk⟩ := hjgone
  have hkt : t ≤ k := by
    by_contra hc
    push Not at hc
    exact (mem_remaining_take h t j).1 hj k hk hc hjk
  have hwin := I3 k hk hkt (by omega)
  simp only [wonBy, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨h[k], List.getElem_mem hk, hwin, hjk⟩

end degenerate

theorem anyPrice_empty {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) :
    anyPrice β w ∅ = 0 := by
  unfold anyPrice
  haveI : IsEmpty {p : Fin m → ℝ // (∀ j ∈ (∅ : Finset (Fin m)), 0 ≤ p j) ∧
      ∑ j ∈ (∅ : Finset (Fin m)), p j = 1} := ⟨fun q => by simpa using q.2.2⟩
  exact Real.iInf_of_isEmpty _


end APSL46Sol

open APSL46Sol in
theorem solution {n m : ℕ} (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n) :
    ∃ σ : Strategy n m,
      Guarantees b σ i v (3 / 5 * anyPrice (b i) (addVal v) Finset.univ) := by
  classical
  have hb0 : ∀ k, 0 ≤ b k := fun k => (hb k).le
  set z := anyPrice (b i) (addVal v) Finset.univ with hzdef
  refine ⟨strat46 v hv b i (3 * z / 5),
    fun h hp hf hne => strat46_legal v hv b hb0 i _ h hp hf hne, ?_⟩
  intro h hp hf hdone
  have hval0 : 0 ≤ addVal v (wonBy i h) := addVal_nonneg v hv _
  rcases le_or_gt z 0 with hz | hz
  · nlinarith
  set θ := 3 * z / 5 with hθ
  have hθpos : 0 < θ := by positivity
  rw [show 3 / 5 * z = θ by rw [hθ]; ring]
  by_cases hW : wonP1 v θ i h
  · exact value_W v hv b i θ hθpos h hp hf hW
  have hph : ¬ phase1 v θ h := by
    intro hph
    have := hph h.length le_rfl
    rw [List.take_length] at this
    unfold cnd at this
    rw [hdone, rankedValue_of_card_lt v ∅ 1 (by simp),
      rankedValue_of_card_lt v ∅ 2 (by simp)] at this
    linarith
  set t := tp v θ h with ht
  set h0 := h.take t with hh0
  obtain ⟨htL, hnc, -⟩ := tp_spec v θ h hph
  obtain ⟨Q1, Q2, hQ, hrangeQ, hQ2, hBle⟩ := stage1 v hv b hb hsum i θ h hp hf hW hph
  have hnw := not_won_before v θ i h hW hph
  have hbi : budget b h0 i = b i :=
    budget_take_of_not_won b i h t htL (fun k hk hkt => hnw k hk hkt)
  have hp0 := validPlay_take b h hp t
  have hnn0 := budget_nonneg b hb0 h0 hp0
  have hBge : budget b h0 i ≤ totalBudget b h0 :=
    Finset.single_le_sum (fun k _ => hnn0 k) (Finset.mem_univ i)
  have hBpos : 0 < totalBudget b h0 := by rw [hbi] at hBge; linarith [hb i]
  set B' := totalBudget b h0 with hB'
  -- a packing at the AnyPrice share `z`
  have hmono : Monotone (addVal v) := fun S T hST =>
    Finset.sum_le_sum_of_subset_of_nonneg hST (fun j _ _ => hv j)
  obtain ⟨lam, h1, h2, h3, h4⟩ := anyPrice_mem_Zset (addVal v) hmono (by simp [addVal]) (b i)
    (hb i) Finset.univ
  -- the remaining items at the end of the first stage
  have hxy : rankedValue v (remaining h0) 1 + rankedValue v (remaining h0) 2 < θ := by
    unfold cnd at hnc; push Not at hnc; exact hnc
  have hy0 := rankedValue_nonneg v hv (remaining h0) 2
  have hM1 : ∀ e, e ∉ Q1 ∪ Q2 → v e < 3 * z / 5 := by
    intro e he
    rw [hrangeQ] at he
    obtain ⟨j1, hj1, hmax⟩ := (remaining h0).exists_max_image v ⟨e, he⟩
    have := rankedValue_one v _ j1 hj1 hmax
    have := hmax e he
    linarith
  have hM2 : ∀ e e', e ∉ Q1 ∪ Q2 → e' ∉ Q1 ∪ Q2 → e ≠ e' → v e + v e' < 3 * z / 5 := by
    intro e e' he he' hne
    rw [hrangeQ] at he he'
    have := pair_le v _ e e' he he' hne
    linarith
  have hrange : ∀ j, j ∉ Q1 ∪ Q2 ↔ ∃ a, ιf h0 a = j :=
    fun j => (hrangeQ j).trans (ιf_range h0 j)
  -- Equation (2)
  have hZ := eq2 v hv (b i) (hb i) z hz lam h1 h2 h3 h4 Q1 Q2 hQ (ιf h0) hrange hQ2 hM1 hM2
    B' hBpos hBle
  set w' := addVal (v ∘ ιf h0) with hw'
  have hmono' : Monotone w' := fun S T hST =>
    Finset.sum_le_sum_of_subset_of_nonneg hST (fun j _ _ => hv _)
  have hbdd : BddAbove (Zset (b i / (2 * B')) w' Finset.univ) := by
    refine ⟨w' Finset.univ, fun c hc => ?_⟩
    obtain ⟨lam', l1, l2, l3, _⟩ := hc
    by_contra hcon
    push Not at hcon
    have : ∀ T ∈ (Finset.univ : Finset (Fin (remaining h0).card)).powerset, lam' T = 0 :=
      fun T hT => l3 T hT (lt_of_le_of_lt (hmono' (Finset.subset_univ T)) hcon)
    rw [Finset.sum_eq_zero this] at l1
    norm_num at l1
  have hAPS : 2 * z / 5 ≤ anyPrice (b i / (2 * B')) w' Finset.univ := by
    rw [← AnyPriceShare.Bidding.proposition_3_2 w' hmono' (by simp [hw', addVal]) _
      (div_pos (hb i) (by linarith)) Finset.univ]
    exact le_csSup hbdd hZ
  have hmapuniv : (Finset.univ : Finset (Fin (remaining h0).card)).map (ιf h0) = remaining h0 := by
    ext j; simp only [Finset.mem_map, Finset.mem_univ, true_and]; exact (ιf_range h0 j).symm
  by_cases hyp : (∀ k, 0 < b2 b i h0 k) ∧ ∑ k, b2 b i h0 k = 1
  · -- the strategy of Lemma 4.7 in the continuation game
    have hh : h0 ++ h.drop t = h := List.take_append_drop t h
    have hT := transfer b hb0 i h0 hp0 (ιf h0) (ιf_range h0) B' hBpos (b2 b i h0)
      (by simp [b2, hB']) (by simp [b2, hB']) (σ'f v hv b i h0) v hv _ (σ'f_spec v hv b i h0 hyp)
      (h.drop t) (by rw [hh]; exact hp) (phase2_follow v hv b i θ h hp hf hW hph hyp)
    have hV := hT.2 (by rw [hh]; exact hdone)
    rw [hh] at hV
    have hb20 : b2 b i h0 0 / 2 = b i / (2 * B') := by
      simp only [b2, Matrix.cons_val_zero, hbi, ← hB']; field_simp
    rw [hb20] at hV
    linarith
  · -- every other agent is out of budget: agent `i` wins all remaining items
    set A := ∑ k ∈ Finset.univ.erase i, budget b h0 k with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => hnn0 k
    have hBA : B' = budget b h0 i + A := by
      rw [hB', hA]; unfold totalBudget; rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hAz : A = 0 := by
      by_contra hne
      have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hne)
      apply hyp
      refine ⟨fun k => ?_, ?_⟩
      · fin_cases k
        · simp only [b2, Fin.zero_eta, Matrix.cons_val_zero, hbi]; exact div_pos (hb i) hBpos
        · simp only [b2, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          exact div_pos hApos hBpos
      · simp only [Fin.sum_univ_two, b2, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← hA, ← add_div, ← hBA, div_self hBpos.ne']
    have hadv : ∀ a, a ≠ i → budget b h0 a = 0 := by
      intro a ha
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnn0 k)).1 hAz a
        (Finset.mem_erase.2 ⟨ha, Finset.mem_univ a⟩)
    have hsub := degenerate_wins v hv b hb0 i θ h hp hf hW hph hyp hadv
      (by rw [hbi]; exact hb i) hdone
    have hvalR : addVal v (remaining h0) ≤ addVal v (wonBy i h) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hv j)
    have hw'univ : w' Finset.univ = addVal v (remaining h0) := by
      rw [hw', addVal_map, hmapuniv]
    have hprop := AnyPriceShare.Bidding.proposition_3_7_proportional (v ∘ ιf h0) (fun _ => hv _)
      (b i / (2 * B')) (div_pos (hb i) (by linarith)) Finset.univ
    have hBi : B' = b i := by rw [hBA, hAz, add_zero, hbi]
    have hprop' : anyPrice (b i / (2 * B')) w' Finset.univ ≤ 1 / 2 * w' Finset.univ := by
      have e : b i / (2 * B') = 1 / 2 := by
        rw [hBi]; have := (hb i).ne'; field_simp
      simp only [proportional] at hprop
      rw [e] at hprop ⊢
      exact hprop
    rw [hw'univ] at hprop'
    linarith
