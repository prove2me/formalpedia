-- Prove2me | solution 1 for AnyPriceShare.Bidding.lemma_D_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T02:17:14.507616+00:00
-- url     : https://prove2.me/submissions/8f79bea6-7839-4ee8-bbd8-0ab07b09189b

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game

open AnyPriceShare.Bidding

namespace APSD3Sol

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


theorem tps_le_prop {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Fin m)) : tps β u S ≤ β * addVal u S := by
  have h := tps_mem u hu β hβ S
  have : β * ∑ j ∈ S, min (u j) (tps β u S) ≤ β * ∑ j ∈ S, u j :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => min_le_left _ _) hβ.le
  unfold addVal; linarith

theorem tps_mono {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (β β' : ℝ) (hβ : 0 < β)
    (hββ' : β ≤ β') (S : Finset (Fin m)) : tps β u S ≤ tps β' u S := by
  have hβ' : 0 < β' := lt_of_lt_of_le hβ hββ'
  have h := tps_mem u hu β hβ S
  have hz := tps_nonneg u hu β hβ S
  by_contra hcon
  push Not at hcon
  have hlt := tps_lt u hu β' hβ' S _ hcon
  have : β * ∑ j ∈ S, min (u j) (tps β u S) ≤ β' * ∑ j ∈ S, min (u j) (tps β u S) :=
    mul_le_mul_of_nonneg_right hββ' (Finset.sum_nonneg fun j _ => le_min (hu j) hz)
  linarith

theorem tps_empty {m : ℕ} (u : Fin m → ℝ) (β : ℝ) : tps β u ∅ = 0 := by
  unfold tps
  have : {z : ℝ | β * ∑ j ∈ (∅ : Finset (Fin m)), min (u j) z = z} = {0} := by
    ext z; simp [eq_comm]
  rw [this, csSup_singleton]

/-- Lemma D.1 (for `K ⊆ S`, including `K = S`). -/
theorem tps_remove {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j)
    (S K : Finset (Fin m)) (hK : K ⊆ S)
    (β : ℝ) (hβ : 0 < β) (hβK : β * ((K.card : ℝ) + 1) ≤ 1) :
    tps β u S ≤ tps (β / (1 - (K.card : ℝ) * β)) u (S \ K) := by
  set z := tps β u S
  set κ : ℝ := (K.card : ℝ) with hκ
  have hκ0 : 0 ≤ κ := Nat.cast_nonneg _
  have hden : β ≤ 1 - κ * β := by linarith
  have hd : 0 < 1 - κ * β := lt_of_lt_of_le hβ hden
  set β' := β / (1 - κ * β)
  have hβ' : 0 < β' := div_pos hβ hd
  have hz0 : 0 ≤ z := tps_nonneg u hu β hβ S
  have hfix : β * ∑ j ∈ S, min (u j) z = z := tps_mem u hu β hβ S
  have hsplit : ∑ j ∈ S, min (u j) z ≤ κ * z + ∑ j ∈ S \ K, min (u j) z := by
    rw [← Finset.sum_sdiff hK]
    have : ∑ j ∈ K, min (u j) z ≤ κ * z := by
      calc ∑ j ∈ K, min (u j) z ≤ ∑ j ∈ K, z := Finset.sum_le_sum fun j _ => min_le_right _ _
        _ = κ * z := by simp [κ]
    linarith
  have hle : z ≤ β' * ∑ j ∈ S \ K, min (u j) z := by
    have h1 : z ≤ β * (κ * z) + β * ∑ j ∈ S \ K, min (u j) z := by
      have := mul_le_mul_of_nonneg_left hsplit hβ.le
      linarith
    have h2 : z * (1 - κ * β) ≤ β * ∑ j ∈ S \ K, min (u j) z := by nlinarith
    simp only [β']
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    linarith
  by_contra hcon
  push Not at hcon
  have := tps_lt u hu β' hβ' (S \ K) z hcon
  linarith

theorem dropped_snoc {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n)
    (g : List (Round n m)) (r : Round n m) :
    lemmaD3DroppedOut u b i (g ++ [r]) ↔
      lemmaD3DroppedOut u b i g ∨ (r.winner = i ∧ lemmaD3Rule u b i g ≤ 2) := by
  constructor
  · rintro ⟨k, hk, hw, hr⟩
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · left
      refine ⟨k, hk', ?_, ?_⟩
      · simpa [List.getElem_append_left hk'] using hw
      · rwa [List.take_append_of_le_length hk'.le] at hr
    · right
      simp at hw hr
      exact ⟨hw, hr⟩
  · rintro (⟨k, hk, hw, hr⟩ | ⟨hw, hr⟩)
    · refine ⟨k, by simp; omega, ?_, ?_⟩
      · simpa [List.getElem_append_left hk] using hw
      · rwa [List.take_append_of_le_length hk.le]
    · exact ⟨g.length, by simp, by simpa using hw, by simpa using hr⟩

theorem rule_cases {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) (g : List (Round n m)) :
    (lemmaD3Rule u b i g = 1 ∧
      budget b g i / totalBudget b g * addVal u (remaining g) ≤ rankedValue u (remaining g) 1) ∨
    (lemmaD3Rule u b i g = 2 ∧
      ¬ budget b g i / totalBudget b g * addVal u (remaining g) ≤ rankedValue u (remaining g) 1 ∧
      2 ≤ (remaining g).card ∧
      rankedValue u (remaining g) 1 < budget b g i / (2 * totalBudget b g - budget b g i) *
        addVal u (remaining g) ∧
      budget b g i / totalBudget b g * addVal u (remaining g) ≤
        rankedValue u (remaining g) 1 + rankedValue u (remaining g) 2) ∨
    (lemmaD3Rule u b i g = 3 ∧
      ¬ budget b g i / totalBudget b g * addVal u (remaining g) ≤ rankedValue u (remaining g) 1 ∧
      ¬ (2 ≤ (remaining g).card ∧
        rankedValue u (remaining g) 1 < budget b g i / (2 * totalBudget b g - budget b g i) *
          addVal u (remaining g) ∧
        budget b g i / totalBudget b g * addVal u (remaining g) ≤
          rankedValue u (remaining g) 1 + rankedValue u (remaining g) 2)) := by
  unfold lemmaD3Rule
  dsimp only
  split_ifs with c1 c2
  · exact Or.inl ⟨rfl, c1⟩
  · exact Or.inr (Or.inl ⟨rfl, c1, c2⟩)
  · exact Or.inr (Or.inr ⟨rfl, c1, c2⟩)

/-- Losing a round in which agent `i` bid `π ≥ x B / s` (rules 1 and 3). -/
theorem lossAlg (bt B s x π k B' s' x' : ℝ) (hbt : 0 ≤ bt) (hbtB : bt ≤ B) (hx : 0 ≤ x)
    (hxs : x ≤ s) (hinv : x * B ≤ bt * s) (hπ : 0 ≤ π) (hπs : x * B ≤ π * s)
    (hB'1 : bt ≤ B') (hB'2 : B' ≤ B - k * π) (hk : 0 ≤ k) (hs' : s - k * x ≤ s')
    (hx'0 : 0 ≤ x') (hx' : x' ≤ x) :
    x' * B' ≤ bt * s' ∧ bt * s / (2 * B - bt) ≤ bt * s' / (2 * B' - bt) := by
  have hs0 : 0 ≤ s := le_trans hx hxs
  have hkπ : 0 ≤ k * π := mul_nonneg hk hπ
  constructor
  · rcases hs0.eq_or_lt with hs00 | hspos
    · have : x = 0 := by rw [← hs00] at hxs; linarith
      have : x' = 0 := by linarith
      rw [this, zero_mul]
      have : s - k * x = 0 := by rw [← hs00]; simp [‹x = 0›]
      nlinarith
    rcases (le_trans hbt hbtB).eq_or_lt with hB0 | hBpos
    · have : B' = 0 := by linarith [le_trans hbt hB'1]
      rw [this, mul_zero]
      have hbt0 : bt = 0 := by linarith
      rw [hbt0, zero_mul]
    -- `k x ≤ s`
    have hkx : k * x * B ≤ s * B := by
      have : k * x * B ≤ k * (π * s) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hπs hk
      nlinarith
    have hkxs : k * x ≤ s := le_of_mul_le_mul_right hkx hBpos
    have hB'0 : 0 ≤ B' := le_trans hbt hB'1
    -- `s x' B' ≤ s x (B - kπ) ≤ x B (s - k x) ≤ bt s (s - k x) ≤ s bt s'`
    have h1 : s * (x' * B') ≤ s * (x * (B - k * π)) := by
      apply mul_le_mul_of_nonneg_left _ hs0
      exact mul_le_mul hx' hB'2 hB'0 hx
    have h2 : s * (x * (B - k * π)) ≤ x * B * (s - k * x) := by
      have : k * x * (x * B) ≤ k * x * (π * s) := mul_le_mul_of_nonneg_left hπs (mul_nonneg hk hx)
      nlinarith
    have h3 : x * B * (s - k * x) ≤ bt * s * (s - k * x) :=
      mul_le_mul_of_nonneg_right hinv (by linarith)
    have h4 : bt * s * (s - k * x) ≤ s * (bt * s') := by
      have := mul_le_mul_of_nonneg_left hs' (mul_nonneg hbt hs0)
      nlinarith
    exact le_of_mul_le_mul_left (by linarith) hspos
  · rcases hbt.eq_or_lt with hbt0 | hbtpos
    · rw [← hbt0]; simp
    have hBpos : 0 < B := lt_of_lt_of_le hbtpos hbtB
    have hB'pos : 0 < B' := lt_of_lt_of_le hbtpos hB'1
    have hD0 : 0 < 2 * B - bt := by linarith
    have hD1 : 0 < 2 * B' - bt := by linarith
    rw [div_le_div_iff₀ hD0 hD1]
    have e1 : s * (2 * B' - bt) ≤ 2 * B * s - 2 * x * B * k - bt * s := by
      have : k * (x * B) ≤ k * (π * s) := mul_le_mul_of_nonneg_left hπs hk
      nlinarith
    have e2 : (s - k * x) * (2 * B - bt) ≤ s' * (2 * B - bt) :=
      mul_le_mul_of_nonneg_right hs' hD0.le
    have e3 : 0 ≤ k * x * bt := mul_nonneg (mul_nonneg hk hx) hbt
    nlinarith

/-- Losing a round in which agent `i` bid `b^(t)/2` under rule 2. -/
theorem rule2LossAlg (bt B s x bw k B' s' x' : ℝ) (hbt : 0 ≤ bt) (hbtB : bt ≤ B) (hx : 0 ≤ x)
    (hs0 : 0 ≤ s) (hrule : x < bt / (2 * B - bt) * s) (hbw : bt / 2 ≤ bw)
    (hB' : B' = B - k * bw) (hB'1 : bt ≤ B') (hk : 0 ≤ k) (hs' : s - k * x ≤ s')
    (hx'0 : 0 ≤ x') (hx' : x' ≤ x) :
    x' * B' ≤ bt * s' ∧ bt * s / (2 * B - bt) ≤ bt * s' / (2 * B' - bt) := by
  rcases hbt.eq_or_lt with hbt0 | hbtpos
  · rw [← hbt0] at hrule; simp at hrule; linarith
  have hBpos : 0 < B := lt_of_lt_of_le hbtpos hbtB
  have hD0 : 0 < 2 * B - bt := by linarith
  have hB'pos : 0 < B' := lt_of_lt_of_le hbtpos hB'1
  have hD1 : 0 < 2 * B' - bt := by linarith
  rw [div_mul_eq_mul_div, lt_div_iff₀ hD0] at hrule
  -- `k b/2 ≤ B - b`
  have hkb : k * bt / 2 ≤ B - bt := by
    have : k * (bt / 2) ≤ k * bw := mul_le_mul_of_nonneg_left hbw hk
    nlinarith
  -- `s' (2B - b) ≥ s (2B - b - k b)`
  have hS1 : s * (2 * B - bt - k * bt) ≤ s' * (2 * B - bt) := by
    have : k * (x * (2 * B - bt)) ≤ k * (bt * s) := mul_le_mul_of_nonneg_left hrule.le hk
    have := mul_le_mul_of_nonneg_right hs' hD0.le
    nlinarith
  have hD1le : 2 * B' - bt ≤ 2 * B - bt - k * bt := by
    have : k * (bt / 2) ≤ k * bw := mul_le_mul_of_nonneg_left hbw hk
    nlinarith
  constructor
  · have h1 : x' * (2 * B - bt) ≤ bt * s := le_trans (mul_le_mul_of_nonneg_right hx' hD0.le) hrule.le
    have h2 : x' * B' * (2 * B - bt) ≤ bt * s * B' := by nlinarith
    have h3 : bt * s * B' ≤ bt * s * (2 * B - bt - k * bt) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hbt hs0)
      nlinarith
    have h4 : bt * s * (2 * B - bt - k * bt) ≤ bt * s' * (2 * B - bt) := by
      have := mul_le_mul_of_nonneg_left hS1 hbt
      nlinarith
    exact le_of_mul_le_mul_right (by linarith) hD0
  · rw [div_le_div_iff₀ hD0 hD1]
    have : s * (2 * B' - bt) ≤ s * (2 * B - bt - k * bt) := mul_le_mul_of_nonneg_left hD1le hs0
    have := mul_le_mul_of_nonneg_left hS1 hbt
    nlinarith

/-- Winning a round under rule 3 (one item of value `x` at price `π = x B / s`). -/
theorem rule3WinAlg (bt B s x π x' : ℝ) (hspos : 0 < s) (hBpos : 0 < B) (hx : 0 ≤ x)
    (hxB : x * B < bt * s) (hbtB : bt ≤ B) (hπs : π * s = x * B) (hx'0 : 0 ≤ x')
    (hcase : (x' ≤ x ∧ 2 * x * B ≤ bt * s) ∨ x' * B ≤ bt * s - x * B) :
    x' * (B - π) ≤ (bt - π) * (s - x) ∧
      bt * s / (2 * B - bt) ≤ x + (bt - π) * (s - x) / (2 * (B - π) - (bt - π)) := by
  have hxs : x < s := by
    by_contra hc; push Not at hc
    have : bt * s ≤ B * s := mul_le_mul_of_nonneg_right hbtB hspos.le
    nlinarith
  have hπB : π < B := by
    by_contra hc; push Not at hc
    have : B * s ≤ π * s := mul_le_mul_of_nonneg_right hc hspos.le
    nlinarith
  have hπbt : π < bt := by
    by_contra hc; push Not at hc
    have : bt * s ≤ π * s := mul_le_mul_of_nonneg_right hc hspos.le
    nlinarith
  have hπ0 : 0 ≤ π := by
    by_contra hc; push Not at hc
    have : π * s < 0 := mul_neg_of_neg_of_pos hc hspos
    nlinarith [mul_nonneg hx hBpos.le]
  constructor
  · rcases hcase with ⟨hx'x, h2⟩ | h3
    · -- `s x (B - π) = x B (s - x) ≤ (b s - x B)(s - x) = s (b - π)(s - x)`
      have e1 : s * (x' * (B - π)) ≤ s * (x * (B - π)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx'x (by linarith)) hspos.le
      have e2 : s * (x * (B - π)) = x * B * (s - x) := by linear_combination (-x) * hπs
      have e3 : x * B * (s - x) ≤ (bt * s - x * B) * (s - x) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have e4 : (bt * s - x * B) * (s - x) = s * ((bt - π) * (s - x)) := by
        linear_combination (s - x) * hπs
      exact le_of_mul_le_mul_left (by linarith) hspos
    · have e1 : s * (x' * (B - π)) * B = x' * B * (B * (s - x)) := by
        linear_combination (-(x' * B)) * hπs
      have e2 : x' * B * (B * (s - x)) ≤ (bt * s - x * B) * (B * (s - x)) :=
        mul_le_mul_of_nonneg_right h3 (mul_nonneg hBpos.le (by linarith))
      have e4 : (bt * s - x * B) * (B * (s - x)) = s * ((bt - π) * (s - x)) * B := by
        linear_combination (B * (s - x)) * hπs
      have : s * (x' * (B - π)) ≤ s * ((bt - π) * (s - x)) :=
        le_of_mul_le_mul_right (by linarith) hBpos
      exact le_of_mul_le_mul_left this hspos
  · have hD0 : 0 < 2 * B - bt := by linarith
    have hD1 : 0 < 2 * (B - π) - (bt - π) := by linarith
    rw [add_div' _ _ _ hD1.ne', div_le_div_iff₀ hD0 hD1]
    have key : (x * (2 * (B - π) - (bt - π)) + (bt - π) * (s - x)) * (2 * B - bt)
        - bt * s * (2 * (B - π) - (bt - π)) = 2 * (B - bt) * (x * (2 * B - bt) - π * s) := by ring
    have : 0 ≤ 2 * (B - bt) * (x * (2 * B - bt) - π * s) := by
      rw [hπs]
      have : x * (2 * B - bt) - x * B = x * (B - bt) := by ring
      rw [this]
      have := mul_nonneg (mul_nonneg hx (sub_nonneg.2 hbtB)) (sub_nonneg.2 hbtB)
      nlinarith
    linarith

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

/-- The target `b^(t) s^(t) / (2 B^(t) − b^(t))` of the second stage. -/
noncomputable def tgt {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n)
    (g : List (Round n m)) : ℝ :=
  budget b g i * addVal u (remaining g) / (2 * totalBudget b g - budget b g i)

/-- First stage: agent `i` has won nothing and the TPS of the current instance (with the
renormalised entitlement) is at least the original TPS. -/
def StA {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) (g : List (Round n m)) : Prop :=
  ¬ lemmaD3DroppedOut u b i g ∧ wonBy i g = ∅ ∧ budget b g i = b i ∧ totalBudget b g ≤ 1 ∧
    tps (b i) u Finset.univ ≤ tps (budget b g i / totalBudget b g) u (remaining g)

/-- Second stage: `x/s ≤ b/B`, and the accumulated value plus the target reaches the goal. -/
def StB {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) (G : ℝ)
    (g : List (Round n m)) : Prop :=
  ¬ lemmaD3DroppedOut u b i g ∧
    rankedValue u (remaining g) 1 * totalBudget b g ≤ budget b g i * addVal u (remaining g) ∧
    G ≤ addVal u (wonBy i g) + tgt u b i g

def Inv {n m : ℕ} (u : Fin m → ℝ) (b : Fin n → ℝ) (i : Fin n) (G : ℝ)
    (g : List (Round n m)) : Prop :=
  G ≤ addVal u (wonBy i g) ∨ StA u b i g ∨ StB u b i G g

theorem step {n m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (b : Fin n → ℝ)
    (hb : ∀ k, 0 < b k) (i : Fin n) (σ : Strategy n m) (hσ : IsLemmaD3Strategy u b i σ)
    (G : ℝ) (hGdef : G = 1 / (2 - b i) * tps (b i) u Finset.univ) (hbi1 : b i ≤ 1)
    (g : List (Round n m)) (r : Round n m)
    (hbud : ∀ k, 0 ≤ budget b g k) (hbud' : ∀ k, 0 ≤ budget b (g ++ [r]) k)
    (hvr : ValidRound b g r) (hbid : r.bids i = (σ g).1)
    (htk : r.winner = i → r.taken = (σ g).2)
    (hinv : Inv u b i G g) : Inv u b i G (g ++ [r]) := by
  classical
  -- quantities before the round
  set R := remaining g with hR
  set s := addVal u R with hs
  set x := rankedValue u R 1 with hx
  set y := rankedValue u R 2 with hy
  set bt := budget b g i with hbt
  set B := totalBudget b g with hB
  set acc := addVal u (wonBy i g) with hacc
  -- quantities after the round
  set R' := remaining (g ++ [r]) with hR'
  set s' := addVal u R' with hs'
  set x' := rankedValue u R' 1 with hx'
  set bt' := budget b (g ++ [r]) i with hbt'
  set B' := totalBudget b (g ++ [r]) with hB'
  set acc' := addVal u (wonBy i (g ++ [r])) with hacc'
  set k : ℝ := (r.taken.card : ℝ) with hk
  have htgt : tgt u b i g = bt * s / (2 * B - bt) := rfl
  have htgt' : tgt u b i (g ++ [r]) = bt' * s' / (2 * B' - bt') := rfl
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hsub : r.taken ⊆ R := hvr.2.2.2.1
  have hRne : R.Nonempty := by
    obtain ⟨j, hj⟩ := hvr.2.2.1; exact ⟨j, hsub hj⟩
  obtain ⟨j1, hj1R, hj1max⟩ := R.exists_max_image u hRne
  have hxj1 : x = u j1 := rankedValue_one u R j1 hj1R hj1max
  have hxmax : ∀ j ∈ R, u j ≤ x := fun j hj => hxj1 ▸ hj1max j hj
  have hx0 : 0 ≤ x := by rw [hxj1]; exact hu j1
  have hs0 : 0 ≤ s := addVal_nonneg u hu R
  have hxs : x ≤ s := by rw [hxj1]; exact Finset.single_le_sum (fun j _ => hu j) hj1R
  have hy0 : 0 ≤ y := rankedValue_nonneg u hu R 2
  have hbt0 : 0 ≤ bt := hbud i
  have hbtB : bt ≤ B := Finset.single_le_sum (fun k _ => hbud k) (Finset.mem_univ i)
  have hRR' : R' = R \ r.taken := remaining_snoc g r
  have hR'sub : R' ⊆ R := by rw [hRR']; exact Finset.sdiff_subset
  have hss' : s' = s - addVal u r.taken := by
    rw [hs', hRR', hs, addVal, addVal, addVal, Finset.sum_sdiff_eq_sub hsub]
  have htakenle : addVal u r.taken ≤ k * x := by
    unfold addVal
    calc ∑ j ∈ r.taken, u j ≤ ∑ j ∈ r.taken, x := Finset.sum_le_sum fun j hj => hxmax j (hsub hj)
      _ = k * x := by simp [hk]
  have hs'ge : s - k * x ≤ s' := by rw [hss']; linarith
  have hs'0 : 0 ≤ s' := addVal_nonneg u hu R'
  have hx'le : x' ≤ x := by
    rw [hxj1]
    exact rankedValue_le_max u hu R' j1 (fun j hj => hj1max j (hR'sub hj)) 1
  have hx'0 : 0 ≤ x' := rankedValue_nonneg u hu R' 1
  have hBB' : B' = B - k * r.bids r.winner := by
    rw [hB', hB]
    unfold totalBudget
    simp only [budget_snoc, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  have hbtbt' : bt' = bt - (if r.winner = i then k * r.bids i else 0) := budget_snoc b g r i
  have hbt'B' : bt' ≤ B' := Finset.single_le_sum (fun k _ => hbud' k) (Finset.mem_univ i)
  have hbt'0 : 0 ≤ bt' := hbud' i
  have hwinbid : r.bids i ≤ r.bids r.winner := hvr.2.1 i
  have hbidi0 : 0 ≤ r.bids i := (hvr.1 i).1
  have hdrop' := dropped_snoc u b i g r
  have hwonne : r.winner ≠ i → acc' = acc := by
    intro hw
    rw [hacc', hacc]
    congr 1
    ext j; rw [mem_wonBy_snoc]; simp [hw]
  have hwoneq : r.winner = i → acc' = acc + addVal u r.taken := by
    intro hw
    have hwon : wonBy i (g ++ [r]) = wonBy i g ∪ r.taken := by
      ext j; rw [mem_wonBy_snoc, Finset.mem_union]; simp [hw]
    have hdisj : Disjoint (wonBy i g) r.taken := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      exact not_mem_remaining_of_mem_wonBy i g j hj (hsub hj')
    rw [hacc', hwon, addVal_union _ _ _ hdisj]
  have hacc_le : acc ≤ acc' := by
    by_cases hw : r.winner = i
    · rw [hwoneq hw]; linarith [addVal_nonneg u hu r.taken]
    · rw [hwonne hw]
  have hσg := hσ g (Finset.nonempty_iff_ne_empty.1 hRne)
  dsimp only at hσg
  obtain ⟨-, hσ1, hσ2, hσ3⟩ := hσg
  have mkD : G ≤ acc' → Inv u b i G (g ++ [r]) := fun h => Or.inl h
  have mkA : ¬ lemmaD3DroppedOut u b i (g ++ [r]) → wonBy i (g ++ [r]) = ∅ → bt' = b i →
      B' ≤ 1 → tps (b i) u Finset.univ ≤ tps (bt' / B') u R' → Inv u b i G (g ++ [r]) :=
    fun h1 h2 h3 h4 h5 => Or.inr (Or.inl ⟨h1, h2, h3, h4, h5⟩)
  have mkB : ¬ lemmaD3DroppedOut u b i (g ++ [r]) → x' * B' ≤ bt' * s' →
      G ≤ acc' + bt' * s' / (2 * B' - bt') → Inv u b i G (g ++ [r]) :=
    fun h1 h2 h3 => Or.inr (Or.inr ⟨h1, h2, h3⟩)
  -- second stage step
  have hBstep : ¬ lemmaD3DroppedOut u b i g → x * B ≤ bt * s → G ≤ acc + tgt u b i g →
      Inv u b i G (g ++ [r]) := by
    intro hnd hI1 hI2
    rw [htgt] at hI2
    rcases rule_cases u b i g with ⟨h1, c1⟩ | ⟨h2, c1, c2, c3, c4⟩ | ⟨h3, c1, c2⟩
    · -- rule 1: bid the whole budget for the top item
      have c1 : bt / B * s ≤ x := c1
      obtain ⟨j, hjR, hjx, hσj⟩ := hσ1 hnd h1
      have hjx : u j = x := hjx
      rw [hσj] at hbid htk
      have hbidv : r.bids i = bt := hbid
      by_cases hw : r.winner = i
      · apply mkD
        have htj : r.taken = {j} := htk hw
        rw [hwoneq hw, htj]
        simp only [addVal, Finset.sum_singleton]
        rw [hjx]
        have : bt * s / (2 * B - bt) ≤ x := by
          rcases (le_trans hbt0 hbtB).eq_or_lt with hB0 | hBpos
          · have : bt = 0 := by linarith
            rw [this]; simp [hx0]
          · calc bt * s / (2 * B - bt) ≤ bt * s / B :=
                  div_le_div_of_nonneg_left (mul_nonneg hbt0 hs0) hBpos (by linarith)
              _ = bt / B * s := by ring
              _ ≤ x := c1
        linarith
      · have hbt'eq : bt' = bt := by rw [hbtbt', if_neg hw, sub_zero]
        obtain ⟨L1, L2⟩ := lossAlg bt B s x bt k B' s' x' hbt0 hbtB hx0 hxs hI1 hbt0 hI1
          (by rw [← hbt'eq]; exact hbt'B')
          (by rw [hBB']; have := mul_le_mul_of_nonneg_left (hbidv ▸ hwinbid) hk0; linarith)
          hk0 hs'ge hx'0 hx'le
        refine mkB ?_ ?_ ?_
        · rw [hdrop']; push Not; exact ⟨hnd, fun h => absurd h hw⟩
        · rw [hbt'eq]; exact L1
        · rw [hbt'eq, hwonne hw]; linarith
    · -- rule 2: bid half the budget for the top two items
      have c3 : x < bt / (2 * B - bt) * s := c3
      have c4 : bt / B * s ≤ x + y := c4
      obtain ⟨j₁, hj₁R, j₂, hj₂R, hne, hj₁x, hj₂y, hσj⟩ := hσ2 hnd h2
      have hj₁x : u j₁ = x := hj₁x
      have hj₂y : u j₂ = y := hj₂y
      rw [hσj] at hbid htk
      have hbidv : r.bids i = bt / 2 := hbid
      by_cases hw : r.winner = i
      · apply mkD
        have htj : r.taken = {j₁, j₂} := htk hw
        rw [hwoneq hw, htj]
        simp only [addVal, Finset.sum_pair hne]
        rw [hj₁x, hj₂y]
        have : bt * s / (2 * B - bt) ≤ x + y := by
          rcases (le_trans hbt0 hbtB).eq_or_lt with hB0 | hBpos
          · have : bt = 0 := by linarith
            rw [this]; simp; linarith
          · calc bt * s / (2 * B - bt) ≤ bt * s / B :=
                  div_le_div_of_nonneg_left (mul_nonneg hbt0 hs0) hBpos (by linarith)
              _ = bt / B * s := by ring
              _ ≤ x + y := c4
        linarith
      · have hbt'eq : bt' = bt := by rw [hbtbt', if_neg hw, sub_zero]
        obtain ⟨L1, L2⟩ := rule2LossAlg bt B s x (r.bids r.winner) k B' s' x' hbt0 hbtB hx0 hs0
          c3 (hbidv ▸ hwinbid) hBB' (by rw [← hbt'eq]; exact hbt'B') hk0 hs'ge hx'0 hx'le
        refine mkB ?_ ?_ ?_
        · rw [hdrop']; push Not; exact ⟨hnd, fun h => absurd h hw⟩
        · rw [hbt'eq]; exact L1
        · rw [hbt'eq, hwonne hw]; linarith
    · -- rule 3: bid `(x/s) B` for the top item
      have c1 : ¬ (bt / B * s ≤ x) := c1
      have c2 : ¬ (2 ≤ R.card ∧ x < bt / (2 * B - bt) * s ∧ bt / B * s ≤ x + y) := c2
      obtain ⟨j, hjR, hjx, hσj⟩ := hσ3 hnd h3
      have hjx : u j = x := hjx
      rw [hσj] at hbid htk
      have hBpos : 0 < B := by
        rcases (le_trans hbt0 hbtB).eq_or_lt with hB0 | hBpos
        · exfalso; apply c1; rw [← hB0]; simp [hx0]
        · exact hBpos
      have hspos : 0 < s := by
        rcases hs0.eq_or_lt with hs00 | hspos
        · exfalso; apply c1; rw [← hs00]; simp [hx0]
        · exact hspos
      have hxB : x * B < bt * s := by
        push Not at c1
        rw [div_mul_eq_mul_div, lt_div_iff₀ hBpos] at c1
        linarith
      set π := x / s * B with hπ
      have hπs : π * s = x * B := by rw [hπ]; field_simp
      have hπ0 : 0 ≤ π := by positivity
      have hbidv : r.bids i = π := hbid
      by_cases hw : r.winner = i
      · have htj : r.taken = {j} := htk hw
        have hk1 : k = 1 := by rw [hk, htj]; simp
        have hwj : r.bids r.winner = π := by rw [hw, hbidv]
        by_cases hdone : bt * s / (2 * B - bt) ≤ x
        · apply mkD
          rw [hwoneq hw, htj]
          simp only [addVal, Finset.sum_singleton]
          rw [hjx]; linarith
        push Not at hdone
        -- after winning: `s' = s - x`, `B' = B - π`, `b' = b - π`, and `x' = y`
        have hs'eq : s' = s - x := by
          rw [hss', htj]; simp [addVal, hjx]
        have hB'eq : B' = B - π := by rw [hBB', hk1, hwj, one_mul]
        have hbt'eq : bt' = bt - π := by rw [hbtbt', if_pos hw, hk1, hbidv, one_mul]
        have hjmax : ∀ j' ∈ R, u j' ≤ u j := fun j' hj' => hjx ▸ hxmax j' hj'
        have hx'y : x' = y := by
          have hR'e : R' = R.erase j := by
            rw [hRR', htj]; ext z; simp [Finset.mem_sdiff, Finset.mem_erase, and_comm]
          rw [hx', hR'e, hy, show (2 : ℕ) = 1 + 1 from rfl,
            rankedValue_succ u R j hjR hjmax 1 le_rfl]
        have hcase : (x' ≤ x ∧ 2 * x * B ≤ bt * s) ∨ x' * B ≤ bt * s - x * B := by
          by_cases h2x : 2 * x * B ≤ bt * s
          · exact Or.inl ⟨hx'le, h2x⟩
          · right
            by_cases hc2 : 2 ≤ R.card
            · have hnot : ¬ (bt / B * s ≤ x + y) := by
                intro hc
                apply c2
                refine ⟨hc2, ?_, hc⟩
                rw [div_mul_eq_mul_div]; exact hdone
              push Not at hnot
              rw [div_mul_eq_mul_div, lt_div_iff₀ hBpos] at hnot
              rw [hx'y]; linarith
            · have : y = 0 := rankedValue_of_card_lt u R 2 (by omega)
              rw [hx'y, this, zero_mul]; linarith
        obtain ⟨W1, W2⟩ := rule3WinAlg bt B s x π x' hspos hBpos hx0 hxB hbtB hπs hx'0 hcase
        refine mkB ?_ ?_ ?_
        · rw [hdrop']; push Not; refine ⟨hnd, fun _ => ?_⟩; rw [h3]; norm_num
        · rw [hB'eq, hbt'eq, hs'eq]; exact W1
        · rw [hwoneq hw, htj, hB'eq, hbt'eq, hs'eq]
          simp only [addVal, Finset.sum_singleton]
          rw [hjx]
          linarith
      · have hbt'eq : bt' = bt := by rw [hbtbt', if_neg hw, sub_zero]
        obtain ⟨L1, L2⟩ := lossAlg bt B s x π k B' s' x' hbt0 hbtB hx0 hxs hI1 hπ0 hπs.symm.le
          (by rw [← hbt'eq]; exact hbt'B')
          (by rw [hBB']; have := mul_le_mul_of_nonneg_left (hbidv ▸ hwinbid) hk0; linarith)
          hk0 hs'ge hx'0 hx'le
        refine mkB ?_ ?_ ?_
        · rw [hdrop']; push Not; exact ⟨hnd, fun h => absurd h hw⟩
        · rw [hbt'eq]; exact L1
        · rw [hbt'eq, hwonne hw]; linarith
  rcases hinv with hD | ⟨hnd, hwon, hbteq, hB1, htps⟩ | ⟨hnd, hI1, hI2⟩
  · exact mkD (le_trans hD hacc_le)
  · have hbteq : bt = b i := hbteq
    have hB1 : B ≤ 1 := hB1
    have htps : tps (b i) u Finset.univ ≤ tps (bt / B) u R := htps
    have hacc0 : acc = 0 := by rw [hacc, hwon]; simp [addVal]
    have hBpos : 0 < B := lt_of_lt_of_le (hbteq ▸ hb i) hbtB
    have hβpos : 0 < bt / B := div_pos (hbteq ▸ hb i) hBpos
    have htpsle : tps (bt / B) u R ≤ bt / B * s := tps_le_prop u hu _ hβpos R
    have hTPS0' : 0 ≤ tps (b i) u Finset.univ := tps_nonneg u hu _ (hb i) _
    have hG : G ≤ tps (b i) u Finset.univ := by
      rw [hGdef, one_div_mul_eq_div]
      exact div_le_self hTPS0' (by linarith)
    by_cases hxB : x * B ≤ bt * s
    · -- the second stage starts now
      apply hBstep hnd hxB
      rw [htgt, hacc0, zero_add]
      have hbiβ : b i ≤ bt / B := by
        rw [hbteq, le_div_iff₀ hBpos]
        have := hb i
        nlinarith
      have hbi1 : bt / B ≤ 1 := (div_le_one hBpos).2 hbtB
      -- `G = TPS/(2 - b_i) ≤ ...`; since `G ≤ TPS ≤ β s` and `β s / (2-β) ≥ β s / ... `
      have hTPS0 : 0 ≤ tps (b i) u Finset.univ := tps_nonneg u hu _ (hb i) _
      have hGle : G ≤ bt / B * s / (2 - bt / B) := by
        have hβs : 0 ≤ bt / B * s := mul_nonneg hβpos.le hs0
        have h2β : 0 < 2 - bt / B := by linarith
        calc G = tps (b i) u Finset.univ / (2 - b i) := by rw [hGdef, one_div_mul_eq_div]
          _ ≤ bt / B * s / (2 - b i) :=
              div_le_div_of_nonneg_right (le_trans htps htpsle) (by linarith)
          _ ≤ bt / B * s / (2 - bt / B) := div_le_div_of_nonneg_left hβs h2β (by linarith)
      have e : bt / B * s / (2 - bt / B) = bt * s / (2 * B - bt) := by
        field_simp
      linarith
    · -- rule 1 is in force
      push Not at hxB
      have c1 : bt / B * s ≤ x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hBpos]; linarith
      have h1 : lemmaD3Rule u b i g = 1 := by
        rcases rule_cases u b i g with ⟨h1, _⟩ | ⟨_, c, _⟩ | ⟨_, c, _⟩
        · exact h1
        · exact absurd c1 c
        · exact absurd c1 c
      obtain ⟨j, hjR, hjx, hσj⟩ := hσ1 hnd h1
      have hjx : u j = x := hjx
      rw [hσj] at hbid htk
      have hbidv : r.bids i = bt := hbid
      by_cases hw : r.winner = i
      · apply mkD
        have htj : r.taken = {j} := htk hw
        rw [hwoneq hw, htj, hacc0]
        simp only [addVal, Finset.sum_singleton, zero_add]
        rw [hjx]
        linarith
      · have hbt'eq : bt' = bt := by rw [hbtbt', if_neg hw, sub_zero]
        have hbt'pos : 0 < bt := hbteq ▸ hb i
        have hkb : k * bt ≤ B - bt' := by
          have := mul_le_mul_of_nonneg_left (hbidv ▸ hwinbid) hk0
          linarith
        have hB'pos : 0 < B' := lt_of_lt_of_le hbt'pos (hbt'eq ▸ hbt'B')
        refine mkA ?_ ?_ ?_ ?_ ?_
        · rw [hdrop']; push Not; exact ⟨hnd, fun h => absurd h hw⟩
        · have : wonBy i (g ++ [r]) = wonBy i g := by
            ext j; rw [mem_wonBy_snoc]; simp [hw]
          rw [this, hwon]
        · rw [← hbteq]; exact hbt'eq
        · have : 0 ≤ k * r.bids r.winner := mul_nonneg hk0 (le_trans hbidi0 hwinbid)
          linarith
        · -- Lemma D.1 and monotonicity of the TPS in the entitlement
          have hK : (r.taken.card : ℝ) = k := rfl
          have hβK : bt / B * ((r.taken.card : ℝ) + 1) ≤ 1 := by
            rw [hK, div_mul_eq_mul_div, div_le_one hBpos]; rw [hbt'eq] at hkb
            have : bt * (k + 1) = k * bt + bt := by ring
            linarith
          have hD1 := tps_remove u hu R r.taken hsub (bt / B) hβpos hβK
          have hden : 0 < 1 - k * (bt / B) := by
            have : k * bt < B := by rw [hbt'eq] at hkb; linarith
            rw [sub_pos, ← mul_div_assoc, div_lt_one hBpos]
            exact this
          have hmono : bt / B / (1 - k * (bt / B)) ≤ bt' / B' := by
            rw [hbt'eq]
            have e : bt / B / (1 - k * (bt / B)) = bt / (B - k * bt) := by
              have : B - k * bt ≠ 0 := by
                have : k * bt < B := by rw [hbt'eq] at hkb; linarith
                linarith
              field_simp
            rw [e]
            apply div_le_div_of_nonneg_left hbt0 hB'pos
            rw [hbt'eq] at hkb
            have := mul_le_mul_of_nonneg_left (hbidv ▸ hwinbid) hk0
            rw [hBB']; linarith
          have hpos' : 0 < bt / B / (1 - k * (bt / B)) := div_pos hβpos hden
          calc tps (b i) u Finset.univ ≤ tps (bt / B) u R := htps
            _ ≤ tps (bt / B / (1 - (r.taken.card : ℝ) * (bt / B))) u (R \ r.taken) := hD1
            _ ≤ tps (bt' / B') u (R \ r.taken) := tps_mono u hu _ _ hpos' hmono _
            _ = tps (bt' / B') u R' := by rw [hRR']
  · have hI1 : x * B ≤ bt * s := hI1
    exact hBstep hnd hI1 hI2

end APSD3Sol

open APSD3Sol in
theorem solution {n m : ℕ} (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n)
    (σ : Strategy n m) (hσ : IsLemmaD3Strategy v b i σ) :
    Guarantees b σ i v (1 / (2 - b i) * tps (b i) v Finset.univ) := by
  classical
  have hb0 : ∀ k, 0 ≤ b k := fun k => (hb k).le
  have hbi1 : b i ≤ 1 := by
    rw [← hsum]; exact Finset.single_le_sum (fun k _ => hb0 k) (Finset.mem_univ i)
  constructor
  · -- every prescribed move is legal
    intro h hp _ hne
    have hbud := budget_nonneg b hb0 h hp
    have hbtB : budget b h i ≤ totalBudget b h :=
      Finset.single_le_sum (fun k _ => hbud k) (Finset.mem_univ i)
    have hσh := hσ h hne
    dsimp only at hσh
    obtain ⟨hσ0, hσ1, hσ2, hσ3⟩ := hσh
    by_cases hd : lemmaD3DroppedOut v b i h
    · obtain ⟨h0, j, hj, h2⟩ := hσ0 hd
      refine ⟨by rw [h0], by rw [h0]; exact hbud i, by rw [h2]; exact Finset.singleton_nonempty j,
        by rw [h2]; exact Finset.singleton_subset_iff.2 hj, by rw [h2, h0]; simpa using hbud i⟩
    rcases rule_cases v b i h with ⟨h1, -⟩ | ⟨h2, -⟩ | ⟨h3, c1, -⟩
    · obtain ⟨j, hj, -, he⟩ := hσ1 hd h1
      rw [he]
      exact ⟨hbud i, le_rfl, Finset.singleton_nonempty j, Finset.singleton_subset_iff.2 hj,
        by simp⟩
    · obtain ⟨j₁, hj₁, j₂, hj₂, hne, -, -, he⟩ := hσ2 hd h2
      rw [he]
      refine ⟨by have := hbud i; positivity, by linarith [hbud i], Finset.insert_nonempty _ _,
        Finset.insert_subset hj₁ (Finset.singleton_subset_iff.2 hj₂), ?_⟩
      rw [Finset.card_pair hne]; push_cast; linarith
    · obtain ⟨j, hj, -, he⟩ := hσ3 hd h3
      rw [he]
      have hx0 := rankedValue_nonneg v hv (remaining h) 1
      have hs0 := addVal_nonneg v hv (remaining h)
      have hB0 : 0 ≤ totalBudget b h := le_trans (hbud i) hbtB
      have hBpos : 0 < totalBudget b h := by
        rcases hB0.eq_or_lt with hB00 | hBpos
        · exfalso; apply c1; rw [← hB00]; simp [hx0]
        · exact hBpos
      have hspos : 0 < addVal v (remaining h) := by
        rcases hs0.eq_or_lt with hs00 | hspos
        · exfalso; apply c1; rw [← hs00]; simp [hx0]
        · exact hspos
      have hlt : rankedValue v (remaining h) 1 / addVal v (remaining h) * totalBudget b h <
          budget b h i := by
        push Not at c1
        rw [div_mul_eq_mul_div, lt_div_iff₀ hBpos] at c1
        rw [div_mul_eq_mul_div, div_lt_iff₀ hspos]
        linarith
      refine ⟨by positivity, hlt.le, Finset.singleton_nonempty j,
        Finset.singleton_subset_iff.2 hj, by simpa using hlt.le⟩
  · intro h hp hf hdone
    set G := 1 / (2 - b i) * tps (b i) v Finset.univ with hGdef
    have key : ∀ t ≤ h.length, Inv v b i G (h.take t) := by
      intro t
      induction t with
      | zero =>
        intro _
        right; left
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rintro ⟨k, hk, -⟩; simp at hk
        · simp [wonBy]
        · simp [budget]
        · simp [totalBudget, budget, hsum]
        · have hrem : remaining ([] : List (Round n m)) = Finset.univ := by simp [remaining]
          simp only [List.take_zero, hrem]
          have : budget b ([] : List (Round n m)) i / totalBudget b ([] : List (Round n m)) = b i := by
            simp [totalBudget, budget, hsum]
          rw [this]
      | succ t ih =>
        intro ht
        have htL : t < h.length := by omega
        rw [take_succ' h t htL]
        have hvr := hp t htL
        have hft := hf t htL
        simp only [List.get_eq_getElem] at hvr hft
        refine step v hv b hb i σ hσ G hGdef hbi1 (h.take t) h[t]
          (budget_take_nonneg b hb0 h hp t htL.le) ?_ hvr hft.1 hft.2 (ih htL.le)
        rw [← take_succ' h t htL]
        exact budget_take_nonneg b hb0 h hp (t + 1) ht
    have hfin := key h.length le_rfl
    rw [List.take_length] at hfin
    have hacc0 := addVal_nonneg v hv (wonBy i h)
    rcases hfin with hD | ⟨-, -, -, -, htps⟩ | ⟨-, -, hI⟩
    · exact hD
    · rw [hdone, tps_empty] at htps
      have : G ≤ 0 := by
        rw [hGdef]
        exact mul_nonpos_of_nonneg_of_nonpos (by apply div_nonneg one_pos.le; linarith) htps
      linarith
    · have : tgt v b i h = 0 := by simp [tgt, hdone, addVal]
      rw [this, add_zero] at hI
      exact hI
