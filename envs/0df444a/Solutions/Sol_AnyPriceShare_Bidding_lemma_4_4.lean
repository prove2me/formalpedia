-- Prove2me | solution 1 for AnyPriceShare.Bidding.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T02:02:30.166789+00:00
-- url     : https://prove2.me/submissions/fea04a9e-e612-4b5a-97b3-e961910d5357

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game

open AnyPriceShare.Bidding

namespace APSL44Sol

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

end APSL44Sol

open APSL44Sol in
theorem solution {n m : ℕ} (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n)
    (k : ℕ) (hk : 0 < k)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ k → addVal v T ≤ b i * addVal v Finset.univ)
    (σ : Strategy n m) (hσ : IsBidYourMaxValue v b i σ) :
    Guarantees b σ i v ((k : ℝ) / (k + 1) * b i * addVal v Finset.univ) := by
  classical
  have hb0 : ∀ k, 0 ≤ b k := fun k => (hb k).le
  set s := addVal v Finset.univ with hs
  have hs0 : 0 ≤ s := addVal_nonneg v hv _
  constructor
  · intro h hp _ hne
    obtain ⟨j, hj, -, hσh⟩ := hσ h hne
    rw [hσh]
    refine ⟨le_min (div_nonneg (hv j) hs0) (budget_nonneg b hb0 h hp i), min_le_right _ _,
      Finset.singleton_nonempty j, Finset.singleton_subset_iff.2 hj, ?_⟩
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    exact min_le_right _ _
  intro h hp hf hdone
  have hval0 := addVal_nonneg v hv (wonBy i h)
  rcases hs0.eq_or_lt with hs00 | hspos
  · rw [← hs00]; simpa using hval0
  set L := h.length
  -- the value of the item agent `i` would take
  let X : List (Round n m) → ℝ := fun g => addVal v (σ g).2
  have hround : ∀ t, t < L → ∃ j ∈ remaining (h.take t),
      (∀ j' ∈ remaining (h.take t), v j' ≤ v j) ∧
      σ (h.take t) = (min (v j / s) (budget b (h.take t) i), {j}) := by
    intro t ht
    have hvr := hp t ht
    simp only [List.get_eq_getElem] at hvr
    have hne : remaining (h.take t) ≠ ∅ := by
      obtain ⟨x, hx⟩ := hvr.2.2.1
      exact Finset.nonempty_iff_ne_empty.1 ⟨x, hvr.2.2.2.1 hx⟩
    exact hσ _ hne
  let P : ℕ → Prop := fun t => t = L ∨ ∃ _ : t < L, budget b (h.take t) i < X (h.take t) / s
  have hPex : ∃ t, P t := ⟨L, Or.inl rfl⟩
  set T := Nat.find hPex with hTdef
  have hTle : T ≤ L := Nat.find_min' hPex (Or.inl rfl)
  have hbefore : ∀ t < T, t < L ∧ X (h.take t) / s ≤ budget b (h.take t) i := by
    intro t ht
    have hns := Nat.find_min hPex ht
    simp only [P, not_or, not_exists, not_lt] at hns
    have htL : t < L := by omega
    exact ⟨htL, hns.2 htL⟩
  -- invariants up to round `T`
  have hinv : ∀ t ≤ T,
      addVal v (wonBy i (h.take t)) = s * (b i - budget b (h.take t) i) ∧
      addVal v (Finset.univ \ remaining (h.take t)) ≤ s * ∑ k, (b k - budget b (h.take t) k) ∧
      (∀ j ∈ wonBy i (h.take t), ∀ j' ∈ remaining (h.take t), v j' ≤ v j) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · simp [wonBy, budget, addVal]
      · simp [remaining, budget, addVal]
      · intro j hj; simp [wonBy] at hj
    | succ t ih =>
      intro htT
      obtain ⟨I1, I2, I3⟩ := ih (by omega)
      obtain ⟨htL, hmaxv⟩ := hbefore t (by omega)
      obtain ⟨j, hjR, hjmax, hσt⟩ := hround t htL
      have hX : X (h.take t) = v j := by simp [X, hσt, addVal]
      rw [hX] at hmaxv
      have hvr := hp t htL
      have hft := hf t htL
      simp only [List.get_eq_getElem] at hvr hft
      set r := h[t]
      have hbid : r.bids i = v j / s := by
        rw [hft.1, hσt]; exact min_eq_left hmaxv
      have hsub : r.taken ⊆ remaining (h.take t) := hvr.2.2.2.1
      rw [take_succ' h t htL]
      refine ⟨?_, ?_, ?_⟩
      · rw [budget_snoc]
        by_cases hw : r.winner = i
        · have htk : r.taken = {j} := by rw [hft.2 hw, hσt]
          have hwon : wonBy i (h.take t ++ [r]) = wonBy i (h.take t) ∪ {j} := by
            ext x
            rw [mem_wonBy_snoc, Finset.mem_union, htk]
            simp [hw]
          have hdisj : Disjoint (wonBy i (h.take t)) {j} := by
            rw [Finset.disjoint_singleton_right]
            exact fun hj' => not_mem_remaining_of_mem_wonBy i _ j hj' hjR
          rw [hwon, addVal_union _ _ _ hdisj, I1, if_pos hw, htk, hbid]
          simp only [addVal, Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul]
          field_simp
          ring
        · have hwon : wonBy i (h.take t ++ [r]) = wonBy i (h.take t) := by
            ext x; rw [mem_wonBy_snoc]; simp [hw]
          rw [hwon, I1, if_neg hw, sub_zero]
      · rw [sum_paid_snoc, remaining_snoc]
        have hset : Finset.univ \ (remaining (h.take t) \ r.taken) =
            (Finset.univ \ remaining (h.take t)) ∪ r.taken := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
          constructor
          · intro hx; by_cases hxR : x ∈ remaining (h.take t)
            · exact Or.inr (by tauto)
            · exact Or.inl hxR
          · rintro (hx | hx)
            · tauto
            · tauto
        have hdisj : Disjoint (Finset.univ \ remaining (h.take t)) r.taken := by
          rw [Finset.disjoint_left]
          intro x hx hx'
          exact (Finset.mem_sdiff.1 hx).2 (hsub hx')
        rw [hset, addVal_union _ _ _ hdisj]
        have htaken : addVal v r.taken ≤ (r.taken.card : ℝ) * v j := by
          unfold addVal
          calc ∑ x ∈ r.taken, v x ≤ ∑ x ∈ r.taken, v j :=
                Finset.sum_le_sum fun x hx => hjmax x (hsub hx)
            _ = (r.taken.card : ℝ) * v j := by simp
        have hwin : r.bids i ≤ r.bids r.winner := hvr.2.1 i
        have hvj : v j = s * r.bids i := by rw [hbid]; field_simp
        have : (r.taken.card : ℝ) * v j ≤ s * ((r.taken.card : ℝ) * r.bids r.winner) := by
          rw [hvj]
          have := mul_le_mul_of_nonneg_left hwin (Nat.cast_nonneg r.taken.card)
          nlinarith
        nlinarith
      · intro x hx x' hx'
        rw [remaining_snoc] at hx'
        have hx'R := (Finset.mem_sdiff.1 hx').1
        rw [mem_wonBy_snoc] at hx
        rcases hx with hx | ⟨hw, hxt⟩
        · exact I3 x hx x' hx'R
        · have htk : r.taken = {j} := by rw [hft.2 hw, hσt]
          rw [htk, Finset.mem_singleton] at hxt
          rw [hxt]; exact hjmax x' hx'R
  obtain ⟨I1, I2, I3⟩ := hinv T le_rfl
  -- the final bundle contains what was won up to round `T`
  have hmono : addVal v (wonBy i (h.take T)) ≤ addVal v (wonBy i h) := by
    unfold addVal
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => hv x
    intro x hx
    simp only [wonBy, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨r, hr, h1, h2⟩ := hx
    exact ⟨r, List.mem_of_mem_take hr, h1, h2⟩
  set bT := budget b (h.take T) i
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hbs : 0 ≤ b i * s := mul_nonneg (hb0 i) hs0
  by_cases hsmallbud : bT ≤ b i / (k + 1)
  · -- enough budget was spent on items of matching value
    have : (k : ℝ) / (k + 1) * b i * s ≤ s * (b i - bT) := by
      have e : (k : ℝ) / (k + 1) * b i * s = s * (b i - b i / (k + 1)) := by
        field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) hs0
    linarith
  push Not at hsmallbud
  have hbTpos : 0 < bT := lt_of_le_of_lt (div_nonneg (hb0 i) hk1.le) hsmallbud
  -- the play is not over at round `T`
  have hTL : T < L := by
    rcases lt_or_eq_of_le hTle with hlt | heq
    · exact hlt
    exfalso
    have hall := I2
    have hbT' : bT = budget b h i := by simp only [bT, heq, L, List.take_length]
    rw [heq, List.take_length, hdone, Finset.sdiff_empty, Finset.sum_sub_distrib, hsum] at hall
    have hge : ∑ k, budget b h k ≥ budget b h i :=
      Finset.single_le_sum (fun k _ => budget_nonneg b hb0 h hp k) (Finset.mem_univ i)
    rw [← hbT'] at hge
    have : s * (1 - ∑ k, budget b h k) < s := by nlinarith
    rw [← hs] at hall
    linarith
  have hlast : bT < X (h.take T) / s := by
    have hspec := Nat.find_spec hPex
    rcases hspec with h1 | ⟨_, h2⟩
    · exact absurd h1 (by rw [← hTdef]; omega)
    · exact h2
  obtain ⟨j, hjR, hjmax, hσT⟩ := hround T hTL
  have hX : X (h.take T) = v j := by simp [X, hσT, addVal]
  rw [hX, lt_div_iff₀ hspos] at hlast
  set F := wonBy i (h.take T)
  have hjF : j ∉ F := fun hj => not_mem_remaining_of_mem_wonBy i _ j hj hjR
  have hover : b i * s < addVal v F + v j := by rw [I1]; nlinarith
  by_cases hcard : F.card < k
  · exfalso
    have := hsmall (insert j F) (by rw [Finset.card_insert_of_notMem hjF]; omega)
    rw [addVal, Finset.sum_insert hjF] at this
    unfold addVal at hover
    linarith
  · push Not at hcard
    have hFge : (F.card : ℝ) * v j ≤ addVal v F := by
      unfold addVal
      calc (F.card : ℝ) * v j = ∑ x ∈ F, v j := by simp
        _ ≤ ∑ x ∈ F, v x := Finset.sum_le_sum fun x hx => I3 x hx j hjR
    have hc : (k : ℝ) ≤ F.card := by exact_mod_cast hcard
    have hfin : (k : ℝ) / (k + 1) * b i * s ≤ addVal v F := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hk1]
      by_cases hab : b i * s ≤ addVal v F
      · nlinarith
      · push Not at hab
        nlinarith [mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hab.le)]
    linarith
