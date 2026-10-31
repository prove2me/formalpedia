-- Prove2me | solution 1 for AnyPriceShare.Bidding.theorem_1_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:47:30.344656+00:00
-- url     : https://prove2.me/submissions/bada22e4-ae93-455c-83cb-074ae4b78056
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game
import Theorems.Thm_AnyPriceShare_Bidding_theorem_4_3
import Theorems.Thm_AnyPriceShare_Bidding_proposition_4_2

open AnyPriceShare.Bidding

namespace APSThm13Sol

theorem validPlay_snoc {n m : ℕ} (b : Fin n → ℝ) (h : List (Round n m)) (r : Round n m)
    (hp : ValidPlay b h) (hr : ValidRound b h r) : ValidPlay b (h ++ [r]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
  · have := hp k hk'
    rw [List.take_append_of_le_length hk'.le]
    simpa [List.getElem_append_left hk'] using this
  · simpa using hr

theorem followedBy_snoc {n m : ℕ} (σ : Strategy n m) (i : Fin n) (h : List (Round n m))
    (r : Round n m) (hp : FollowedBy σ i h) (h1 : r.bids i = (σ h).1)
    (h2 : r.winner = i → r.taken = (σ h).2) : FollowedBy σ i (h ++ [r]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
  · have := hp k hk'
    rw [List.take_append_of_le_length hk'.le]
    simpa [List.getElem_append_left hk'] using this
  · simpa using And.intro h1 h2

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

/-- Playing the Bidding Game with every agent following her strategy, starting from any
consistent history, reaches a complete play. -/
theorem exists_complete {n m : ℕ} (b : Fin n → ℝ) (σ : Fin n → Strategy n m) (w : Fin n)
    (hleg : ∀ i h, ValidPlay b h → FollowedBy (σ i) i h → remaining h ≠ ∅ →
      LegalMove b h i (σ i h)) :
    ∀ N, ∀ h : List (Round n m), (remaining h).card = N → ValidPlay b h →
      (∀ i, FollowedBy (σ i) i h) →
      (∀ i i' j, j ∈ wonBy i h → j ∈ wonBy i' h → i = i') →
      ∃ h', ValidPlay b h' ∧ (∀ i, FollowedBy (σ i) i h') ∧ remaining h' = ∅ ∧
        (∀ i i' j, j ∈ wonBy i h' → j ∈ wonBy i' h' → i = i') := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro h hN hp hf hu
    by_cases he : remaining h = ∅
    · exact ⟨h, hp, hf, he, hu⟩
    obtain ⟨win, -, hwin⟩ :=
      Finset.exists_max_image Finset.univ (fun k => (σ k h).1) ⟨w, Finset.mem_univ _⟩
    have hL : ∀ k, LegalMove b h k (σ k h) := fun k => hleg k h hp (hf k) he
    let r : Round n m := ⟨fun k => (σ k h).1, win, (σ win h).2⟩
    have hr : ValidRound b h r := by
      refine ⟨fun k => ⟨(hL k).1, (hL k).2.1⟩, fun k => hwin k (Finset.mem_univ _),
        (hL win).2.2.1, (hL win).2.2.2.1, (hL win).2.2.2.2⟩
    have hsub : r.taken ⊆ remaining h := (hL win).2.2.2.1
    have hlt : (remaining (h ++ [r])).card < N := by
      rw [remaining_snoc, ← hN]
      exact Finset.card_lt_card (Finset.sdiff_ssubset hsub (hL win).2.2.1)
    refine ih _ hlt (h ++ [r]) rfl (validPlay_snoc b h r hp hr) ?_ ?_
    · intro i
      refine followedBy_snoc (σ i) i h r (hf i) rfl ?_
      intro hw
      simp only [r] at hw ⊢
      rw [hw]
    · intro i i' j h1 h2
      rw [mem_wonBy_snoc] at h1 h2
      rcases h1 with h1 | ⟨h1w, h1j⟩ <;> rcases h2 with h2 | ⟨h2w, h2j⟩
      · exact hu i i' j h1 h2
      · exact absurd (hsub h2j) (not_mem_remaining_of_mem_wonBy i h j h1)
      · exact absurd (hsub h1j) (not_mem_remaining_of_mem_wonBy i' h j h2)
      · exact h1w.symm.trans h2w

theorem addVal_mono {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) {S T : Finset (Fin m)}
    (hST : S ⊆ T) : addVal u S ≤ addVal u T := by
  unfold addVal
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun j _ _ => hu j)

theorem addVal_nonneg {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j) (S : Finset (Fin m)) :
    0 ≤ addVal u S := Finset.sum_nonneg (fun j _ => hu j)

end APSThm13Sol

open APSThm13Sol in
theorem solution {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) (hsum : ∑ i, b i = 1) :
    ∃ σ : Fin m → Fin n, ∀ i : Fin n,
      max (3 / 5) (1 / (2 - b i)) * anyPrice (b i) (addVal (v i)) Finset.univ
        ≤ addVal (v i) (allocBundle σ i) := by
  -- there is at least one agent
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hsum
    · exact h0
  let w : Fin n := ⟨0, hn⟩
  -- every agent has a strategy as in Theorem 4.3
  have hstrat := fun i => theorem_4_3 v hv b hb hsum i
  choose σ hσ using hstrat
  obtain ⟨h, hp, hf, hcomplete, huniq⟩ :=
    exists_complete b σ w (fun i h hp hf he => (hσ i).1 h hp hf he)
      _ [] rfl (fun k hk => by simp at hk) (fun i k hk => by simp at hk)
      (fun i i' j h1 => by simp [wonBy] at h1)
  -- the allocation: each item goes to the agent who won it
  classical
  let τ : Fin m → Fin n := fun j => if hj : ∃ i, j ∈ wonBy i h then hj.choose else w
  refine ⟨τ, fun i => ?_⟩
  have hsubset : wonBy i h ⊆ allocBundle τ i := by
    intro j hj
    have hex : ∃ i, j ∈ wonBy i h := ⟨i, hj⟩
    simp only [allocBundle, Finset.mem_filter, Finset.mem_univ, true_and, τ, dif_pos hex]
    exact huniq _ _ j hex.choose_spec hj
  have hguar := (hσ i).2 h hp (hf i) hcomplete
  have hval : addVal (v i) (wonBy i h) ≤ addVal (v i) (allocBundle τ i) :=
    addVal_mono (v i) (hv i) hsubset
  have hval0 : 0 ≤ addVal (v i) (allocBundle τ i) := addVal_nonneg (v i) (hv i) _
  have hbi1 : b i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => (hb k).le) (Finset.mem_univ i)
  have hc : 0 < 1 / (2 - b i) := by
    apply div_pos one_pos; linarith
  have h42 := proposition_4_2 (v i) (hv i) (b i) (hb i) Finset.univ
  set A := anyPrice (b i) (addVal (v i)) Finset.univ
  set T := tps (b i) (v i) Finset.univ
  set c := 1 / (2 - b i)
  rcases le_or_gt A 0 with hA | hA
  · have : max (3 / 5) c * A ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_max_of_le_left (by norm_num)) hA
    linarith
  · have hg1 : 3 / 5 * A ≤ addVal (v i) (wonBy i h) :=
      le_trans (le_max_of_le_left (le_max_left _ _)) hguar
    have hg2 : c * T ≤ addVal (v i) (wonBy i h) :=
      le_trans (le_max_of_le_left (le_max_right _ _)) hguar
    have hcA : c * A ≤ c * T := mul_le_mul_of_nonneg_left h42 hc.le
    rw [max_mul_of_nonneg _ _ hA.le]
    exact max_le (by linarith) (by linarith)
