-- Prove2me | solution 1 for AdInterm.SPE.lemma_2_1_A
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:33:48.80364+00:00
-- url     : https://prove2.me/submissions/6a5f59b2-0382-42f8-8543-47a7e9a05a6e

import Mathlib
import Definitions.Def_AdInterm_SPE_Setting

open MeasureTheory

namespace AdInterm.SPE.L21A

open AdInterm.SPE

variable {k : ℕ → ℕ} {σ : Profile} {v : ℕ → ℝ}

/-- The natural (non-overridden) report of tier-`(s+1)` node `i`. -/
noncomputable def natRep (k : ℕ → ℕ) (σ : Profile) (v : ℕ → ℝ) (ov : BidOverride)
    (s i : ℕ) : WithBot ℝ :=
  if (σ (s + 1) i).1 ≤ (Finset.range (k (s + 1))).sup
      (fun c => bidCore k σ v ov s (i * k (s + 1) + c)) then
    ((σ (s + 1) i).2 (((Finset.range (k (s + 1))).sup
      (fun c => bidCore k σ v ov s (i * k (s + 1) + c))).getD 0) : WithBot ℝ) else ⊥

lemma bidCore_zero_of_eq (b : ℝ) (j : ℕ) :
    bidCore k σ v (some (0, j, b)) 0 j = (b : WithBot ℝ) := by
  simp [bidCore]

lemma bidCore_zero_of_ne (ov : BidOverride) (j : ℕ) (h : ∀ b, ov ≠ some (0, j, b)) :
    bidCore k σ v ov 0 j = (v j : WithBot ℝ) := by
  rcases ov with _ | ⟨s, i, b⟩
  · simp [bidCore]
  · cases s with
    | zero =>
      have : i ≠ j := by
        rintro rfl; exact h b rfl
      simp [bidCore, this]
    | succ s => simp [bidCore]

lemma bidCore_succ_of_eq (b : ℝ) (s j : ℕ) :
    bidCore k σ v (some (s + 1, j, b)) (s + 1) j = (b : WithBot ℝ) := by
  simp [bidCore]

lemma bidCore_succ_of_ne (ov : BidOverride) (s j : ℕ) (h : ∀ b, ov ≠ some (s + 1, j, b)) :
    bidCore k σ v ov (s + 1) j = natRep k σ v ov s j := by
  rcases ov with _ | ⟨s', i, b⟩
  · simp [bidCore, natRep]
  · have : ¬ (s' = s + 1 ∧ i = j) := by
      rintro ⟨rfl, rfl⟩; exact h b rfl
    simp only [bidCore, natRep]
    rw [if_neg this]

lemma bidCore_self (b : ℝ) (t j : ℕ) :
    bidCore k σ v (some (t, j, b)) t j = (b : WithBot ℝ) := by
  cases t with
  | zero => exact bidCore_zero_of_eq b j
  | succ t => exact bidCore_succ_of_eq b t j

lemma bestChild_unique {n : ℕ} {rS : ℝ} {ov : BidOverride} {s p c c' : ℕ}
    (h : IsBestChild k n σ rS v ov s p c) (h' : IsBestChild k n σ rS v ov s p c') :
    c = c' := by
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · exfalso
    have h1 := h'.2.2.2 c h.1
    rw [if_pos hlt] at h1
    have h2 := h.2.2.2 c' h'.1
    rw [if_neg (by omega)] at h2
    exact lt_irrefl _ (lt_of_lt_of_le h1 h2)
  · exact heq
  · exfalso
    have h1 := h.2.2.2 c' h'.1
    rw [if_pos hgt] at h1
    have h2 := h'.2.2.2 c h.1
    rw [if_neg (by omega)] at h2
    exact lt_irrefl _ (lt_of_lt_of_le h1 h2)

lemma chooseChild_some {n : ℕ} {rS : ℝ} {ov : BidOverride} {s p q : ℕ}
    (h : chooseChild k n σ rS v ov s p = some q) :
    ∃ c, IsBestChild k n σ rS v ov s p c ∧ q = p * k (s + 1) + c := by
  classical
  unfold chooseChild at h
  split_ifs at h with hc
  · exact ⟨_, Classical.choose_spec hc, (Option.some.inj h).symm⟩

lemma chooseChild_of_best {n : ℕ} {rS : ℝ} {ov : BidOverride} {s p c : ℕ}
    (h : IsBestChild k n σ rS v ov s p c) :
    chooseChild k n σ rS v ov s p = some (p * k (s + 1) + c) := by
  classical
  have hc : ∃ c, IsBestChild k n σ rS v ov s p c := ⟨c, h⟩
  unfold chooseChild
  rw [dif_pos hc]
  rw [bestChild_unique (Classical.choose_spec hc) h]

lemma chooseChild_none {n : ℕ} {rS : ℝ} {ov : BidOverride} {s p : ℕ}
    (h : ¬ ∃ c, IsBestChild k n σ rS v ov s p c) :
    chooseChild k n σ rS v ov s p = none := by
  classical
  unfold chooseChild
  rw [dif_neg h]

lemma chooseChild_congr {n : ℕ} {rS : ℝ} {v' : ℕ → ℝ} {ov ov' : BidOverride} {s : ℕ}
    (h : bidCore k σ v ov s = bidCore k σ v' ov' s) (p : ℕ) :
    chooseChild k n σ rS v ov s p = chooseChild k n σ rS v' ov' s p := by
  have hb : ∀ c, IsBestChild k n σ rS v ov s p c ↔ IsBestChild k n σ rS v' ov' s p c := by
    intro c; simp only [IsBestChild, h]
  by_cases hc : ∃ c, IsBestChild k n σ rS v ov s p c
  · obtain ⟨c, hc⟩ := hc
    rw [chooseChild_of_best hc, chooseChild_of_best ((hb c).1 hc)]
  · rw [chooseChild_none hc, chooseChild_none (fun ⟨c, hc'⟩ => hc ⟨c, (hb c).2 hc'⟩)]

lemma winnerDepth_congr {n : ℕ} {rS : ℝ} {v' : ℕ → ℝ} {ov ov' : BidOverride} {t : ℕ}
    (h : ∀ s, t ≤ s → bidCore k σ v ov s = bidCore k σ v' ov' s) :
    ∀ d, d ≤ n + 1 - t →
      winnerDepth k n σ rS v ov d = winnerDepth k n σ rS v' ov' d := by
  intro d
  induction d with
  | zero => intro _; simp [winnerDepth]
  | succ d ih =>
    intro hd
    simp only [winnerDepth]
    rw [ih (by omega)]
    congr 1
    funext p
    exact chooseChild_congr (h (n - d) (by omega)) p


/-- `(s, i)` is an ancestor-or-self of `(t, j)` (for `s ≥ t`). -/
def isAnc (k : ℕ → ℕ) (t j s i : ℕ) : Prop := j / ∏ x ∈ Finset.Icc (t + 1) s, k x = i

lemma div_child {K p c : ℕ} (hc : c < K) : (p * K + c) / K = p := by
  have hK : 0 < K := by omega
  rw [mul_comm, Nat.mul_add_div hK, Nat.div_eq_of_lt hc, add_zero]

lemma isAnc_self (t j : ℕ) : isAnc k t j t j := by
  unfold isAnc
  rw [Finset.Icc_eq_empty (by omega)]
  simp

lemma isAnc_self_iff (t j i : ℕ) : isAnc k t j t i ↔ j = i := by
  unfold isAnc
  rw [Finset.Icc_eq_empty (by omega)]
  simp

lemma isAnc_parent {t j s p c : ℕ} (hs : t ≤ s) (hc : c < k (s + 1))
    (h : isAnc k t j s (p * k (s + 1) + c)) : isAnc k t j (s + 1) p := by
  unfold isAnc at *
  rw [Finset.prod_Icc_succ_top (by omega), ← Nat.div_div_eq_div_mul, h, div_child hc]

lemma desc_parent {s i c x : ℕ} (hc : c < k (s + 1))
    (h : DescendantBuyer k s (i * k (s + 1) + c) x) : DescendantBuyer k (s + 1) i x := by
  unfold DescendantBuyer at *
  rw [Finset.prod_Icc_succ_top (by omega), ← Nat.div_div_eq_div_mul, h, div_child hc]

lemma natRep_congr {v' : ℕ → ℝ} {ov ov' : BidOverride} {s i : ℕ}
    (h : ∀ c, c < k (s + 1) →
      bidCore k σ v ov s (i * k (s + 1) + c) = bidCore k σ v' ov' s (i * k (s + 1) + c)) :
    natRep k σ v ov s i = natRep k σ v' ov' s i := by
  unfold natRep
  have : (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov s (i * k (s + 1) + c)) =
      (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v' ov' s (i * k (s + 1) + c)) :=
    Finset.sup_congr rfl (fun c hc => h c (Finset.mem_range.1 hc))
  rw [this]

lemma natRep_mono {ov ov' : BidOverride} {s i : ℕ} (hm : IsMech (σ (s + 1) i))
    (h : ∀ c, c < k (s + 1) →
      bidCore k σ v ov s (i * k (s + 1) + c) ≤ bidCore k σ v ov' s (i * k (s + 1) + c)) :
    natRep k σ v ov s i ≤ natRep k σ v ov' s i := by
  unfold natRep
  have hw : (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov s (i * k (s + 1) + c)) ≤
      (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov' s (i * k (s + 1) + c)) :=
    Finset.sup_mono_fun (fun c hc => h c (Finset.mem_range.1 hc))
  generalize (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov s (i * k (s + 1) + c))
    = w at hw ⊢
  generalize (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov' s (i * k (s + 1) + c))
    = w' at hw ⊢
  split_ifs with h1 h2
  · obtain ⟨a, rfl⟩ : ∃ a : ℝ, (a : WithBot ℝ) = w :=
      WithBot.ne_bot_iff_exists.1 (fun hb => by rw [hb] at h1; exact absurd h1 (by simp))
    obtain ⟨a', rfl⟩ : ∃ a : ℝ, (a : WithBot ℝ) = w' :=
      WithBot.ne_bot_iff_exists.1 (fun hb => by rw [hb] at h2; exact absurd h2 (by simp))
    have h1' : (σ (s + 1) i).1 ≤ a := WithBot.coe_le_coe.1 h1
    have hw' : a ≤ a' := WithBot.coe_le_coe.1 hw
    exact WithBot.coe_le_coe.2
      (hm.2.1 (Set.mem_Ici.2 (le_trans hm.1 h1')) (Set.mem_Ici.2 (le_trans (le_trans hm.1 h1') hw')) hw')
  · exact absurd (le_trans h1 hw) h2
  all_goals exact bot_le

/-- Nodes not above the overridden node at the same or a lower tier are unaffected. -/
lemma bidCore_low (t' j' : ℕ) (b : ℝ) :
    ∀ s i, (s < t' ∨ (s = t' ∧ i ≠ j')) →
      bidCore k σ v (some (t', j', b)) s i = bidCore k σ v none s i := by
  intro s
  induction s with
  | zero =>
    intro i hi
    rw [bidCore_zero_of_ne _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega),
      bidCore_zero_of_ne _ _ (fun b' h => by simp at h)]
  | succ s ih =>
    intro i hi
    rw [bidCore_succ_of_ne _ _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega),
      bidCore_succ_of_ne _ _ _ (fun b' h => by simp at h)]
    exact natRep_congr (fun c _ => ih _ (Or.inl (by omega)))

lemma bidCore_unaffected (t j : ℕ) (b : ℝ) :
    ∀ s, t ≤ s → ∀ i, ¬ isAnc k t j s i →
      bidCore k σ v (some (t, j, b)) s i = bidCore k σ v none s i := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    intro i hi
    rw [isAnc_self_iff] at hi
    exact bidCore_low t j b t i (Or.inr ⟨rfl, fun h => hi h.symm⟩)
  | succ s hs ih =>
    intro i hi
    rw [bidCore_succ_of_ne _ _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega),
      bidCore_succ_of_ne _ _ _ (fun b' h => by simp at h)]
    exact natRep_congr (fun c hc => ih _ (fun h => hi (isAnc_parent hs hc h)))

lemma bidCore_mono {n : ℕ} (hσ : ∀ s i, 1 ≤ s → s ≤ n → IsMech (σ s i))
    (t j : ℕ) {b b' : ℝ} (hbb : b ≤ b') :
    ∀ s, t ≤ s → s ≤ n → ∀ i, isAnc k t j s i →
      bidCore k σ v (some (t, j, b)) s i ≤ bidCore k σ v (some (t, j, b')) s i := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    intro _ i hi
    rw [isAnc_self_iff] at hi
    subst hi
    rw [bidCore_self, bidCore_self]
    exact WithBot.coe_le_coe.2 hbb
  | succ s hs ih =>
    intro hsn i hi
    rw [bidCore_succ_of_ne _ _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega),
      bidCore_succ_of_ne _ _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega)]
    apply natRep_mono (hσ _ _ (by omega) hsn)
    intro c hc
    by_cases ha : isAnc k t j s (i * k (s + 1) + c)
    · exact ih (by omega) _ ha
    · rw [bidCore_unaffected t j b s hs _ ha, bidCore_unaffected t j b' s hs _ ha]

lemma bidCore_selfEq (t j : ℕ) (b0 : ℝ) (hb0 : (b0 : WithBot ℝ) = bidCore k σ v none t j) :
    ∀ s, bidCore k σ v (some (t, j, b0)) s = bidCore k σ v none s := by
  intro s
  induction s with
  | zero =>
    funext i
    by_cases h : t = 0 ∧ i = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [bidCore_self, hb0]
    · rw [bidCore_zero_of_ne _ _ (fun b' h' => by
            simp only [Option.some.injEq, Prod.mk.injEq] at h'
            omega),
        bidCore_zero_of_ne _ _ (fun b' h => by simp at h)]
  | succ s ih =>
    funext i
    by_cases h : t = s + 1 ∧ i = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [bidCore_self, hb0]
    · rw [bidCore_succ_of_ne _ _ _ (fun b' h' => by
            simp only [Option.some.injEq, Prod.mk.injEq] at h'
            omega),
        bidCore_succ_of_ne _ _ _ (fun b' h => by simp at h)]
      exact natRep_congr (fun c _ => by rw [ih])

lemma bidCore_local {v' : ℕ → ℝ} (ov : BidOverride) :
    ∀ s i, (∀ x, DescendantBuyer k s i x → v x = v' x) →
      bidCore k σ v ov s i = bidCore k σ v' ov s i := by
  intro s
  induction s with
  | zero =>
    intro i hi
    by_cases h : ∃ b, ov = some (0, i, b)
    · obtain ⟨b, rfl⟩ := h
      rw [bidCore_zero_of_eq, bidCore_zero_of_eq]
    · push Not at h
      rw [bidCore_zero_of_ne _ _ h, bidCore_zero_of_ne _ _ h]
      rw [hi i (by unfold DescendantBuyer; simp)]
  | succ s ih =>
    intro i hi
    by_cases h : ∃ b, ov = some (s + 1, i, b)
    · obtain ⟨b, rfl⟩ := h
      rw [bidCore_succ_of_eq, bidCore_succ_of_eq]
    · push Not at h
      rw [bidCore_succ_of_ne _ _ _ h, bidCore_succ_of_ne _ _ _ h]
      exact natRep_congr (fun c hc => ih _ (fun x hx => hi x (desc_parent hc hx)))

lemma bidCore_indep {v' : ℕ → ℝ} (t j : ℕ) (b : ℝ)
    (hv : ∀ i, ¬ DescendantBuyer k t j i → v i = v' i) :
    ∀ s, t ≤ s → bidCore k σ v (some (t, j, b)) s = bidCore k σ v' (some (t, j, b)) s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    funext i
    by_cases h : i = j
    · subst h
      rw [bidCore_self, bidCore_self]
    · apply bidCore_local
      intro x hx
      apply hv
      unfold DescendantBuyer at *
      rw [hx]; exact h
  | succ s hs ih =>
    funext i
    rw [bidCore_succ_of_ne _ _ _ (fun b' h' => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          omega),
      bidCore_succ_of_ne _ _ _ (fun b' h' => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          omega)]
    exact natRep_congr (fun c _ => by rw [ih])


lemma winnerDepth_succ_some {n : ℕ} {rS : ℝ} {ov : BidOverride} {d q : ℕ}
    (h : winnerDepth k n σ rS v ov (d + 1) = some q) :
    ∃ p, winnerDepth k n σ rS v ov d = some p ∧
      chooseChild k n σ rS v ov (n - d) p = some q := by
  simp only [winnerDepth] at h
  cases hw : winnerDepth k n σ rS v ov d with
  | none => rw [hw] at h; simp at h
  | some p => rw [hw] at h; exact ⟨p, rfl, h⟩

lemma winner_chain {n : ℕ} {rS : ℝ} {ov : BidOverride} {t j : ℕ} (ht : t ≤ n)
    (hw : winnerDepth k n σ rS v ov (n + 1 - t) = some j) :
    ∀ e d, d + e = n + 1 - t →
      ∃ p, winnerDepth k n σ rS v ov d = some p ∧ isAnc k t j (n + 1 - d) p := by
  intro e
  induction e with
  | zero =>
    intro d hd
    refine ⟨j, by rw [show d = n + 1 - t by omega]; exact hw, ?_⟩
    rw [show n + 1 - d = t by omega]
    exact isAnc_self t j
  | succ e ih =>
    intro d hd
    obtain ⟨q, hq, hqa⟩ := ih (d + 1) (by omega)
    obtain ⟨p, hp, hc⟩ := winnerDepth_succ_some hq
    obtain ⟨c, hbest, rfl⟩ := chooseChild_some hc
    refine ⟨p, hp, ?_⟩
    rw [show n + 1 - (d + 1) = n - d by omega] at hqa
    rw [show n + 1 - d = n - d + 1 by omega]
    exact isAnc_parent (by omega) hbest.1 hqa

lemma winsWith_upset {n : ℕ} (hσ : ∀ s i, 1 ≤ s → s ≤ n → IsMech (σ s i))
    {rS : ℝ} {t j : ℕ} (ht : t ≤ n) {b b' : ℝ} (hbb : b ≤ b')
    (hw : winsWith k n σ rS v t j b) : winsWith k n σ rS v t j b' := by
  unfold winsWith winnerAt at *
  have key : ∀ d, d ≤ n + 1 - t →
      winnerDepth k n σ rS v (some (t, j, b)) d = winnerDepth k n σ rS v (some (t, j, b')) d := by
    intro d
    induction d with
    | zero => intro _; simp [winnerDepth]
    | succ d ih =>
      intro hd
      obtain ⟨p, hp, _⟩ := winner_chain ht hw (n + 1 - t - d) d (by omega)
      obtain ⟨q, hq, hqa⟩ := winner_chain ht hw (n + 1 - t - (d + 1)) (d + 1) (by omega)
      obtain ⟨p', hp', hc⟩ := winnerDepth_succ_some hq
      rw [hp] at hp'
      cases hp'
      obtain ⟨c0, hbest, rfl⟩ := chooseChild_some hc
      rw [show n + 1 - (d + 1) = n - d by omega] at hqa
      have hs1 : t ≤ n - d := by omega
      have hmono := bidCore_mono (v := v) hσ t j hbb (n - d) hs1 (by omega) _ hqa
      have hsib : ∀ d', d' < k (n - d + 1) → d' ≠ c0 →
          bidCore k σ v (some (t, j, b')) (n - d) (p * k (n - d + 1) + d') =
            bidCore k σ v (some (t, j, b)) (n - d) (p * k (n - d + 1) + d') := by
        intro d' _ hne
        have hna : ¬ isAnc k t j (n - d) (p * k (n - d + 1) + d') := by
          intro ha
          unfold isAnc at ha hqa
          rw [ha] at hqa
          omega
        rw [bidCore_unaffected t j b' _ hs1 _ hna, bidCore_unaffected t j b _ hs1 _ hna]
      have hbest' : IsBestChild k n σ rS v (some (t, j, b')) (n - d) p c0 := by
        refine ⟨hbest.1, ?_, ?_, ?_⟩
        · intro hb
          rw [hb] at hmono
          exact hbest.2.1 (le_bot_iff.1 hmono)
        · intro hn
          exact le_trans (hbest.2.2.1 hn) hmono
        · intro d' hd'
          by_cases he : d' = c0
          · subst he
            simp
          · have h0 := hbest.2.2.2 d' hd'
            rw [hsib d' hd' he]
            split_ifs with hlt
            · rw [if_pos hlt] at h0
              exact lt_of_lt_of_le h0 hmono
            · rw [if_neg hlt] at h0
              exact le_trans h0 hmono
      simp only [winnerDepth]
      rw [← ih (by omega), hp]
      simp only [Option.bind_some]
      rw [hc, chooseChild_of_best hbest']
  rw [← key _ le_rfl]
  exact hw

lemma wins_report {n : ℕ} (hσ : ∀ s i, 1 ≤ s → s ≤ n → IsMech (σ s i))
    {rS : ℝ} (hrS : 0 ≤ rS) {t j : ℕ} (ht : t ≤ n)
    (hw : wins k n σ rS v t j) :
    ∃ b0 : ℝ, 0 ≤ b0 ∧ (b0 : WithBot ℝ) = bidCore k σ v none t j := by
  unfold wins winnerAt at hw
  rw [show n + 1 - t = (n - t) + 1 by omega] at hw
  obtain ⟨p, hp, hc⟩ := winnerDepth_succ_some hw
  rw [show n - (n - t) = t by omega] at hc
  obtain ⟨c0, hbest, hj⟩ := chooseChild_some hc
  obtain ⟨b0, hb0⟩ := WithBot.ne_bot_iff_exists.1 hbest.2.1
  rw [← hj] at hb0
  refine ⟨b0, ?_, hb0⟩
  rcases Nat.eq_or_lt_of_le ht with heq | hlt
  · have := hbest.2.2.1 heq
    rw [← hj, ← hb0] at this
    exact le_trans hrS (WithBot.coe_le_coe.1 this)
  · rw [show n - t = (n - t - 1) + 1 by omega] at hp
    obtain ⟨p', _, hc'⟩ := winnerDepth_succ_some hp
    rw [show n - (n - t - 1) = t + 1 by omega] at hc'
    obtain ⟨c1, hbest1, hp'⟩ := chooseChild_some hc'
    have hne := hbest1.2.1
    rw [← hp', bidCore_succ_of_ne _ _ _ (fun b h => by simp at h)] at hne
    unfold natRep at hne
    split_ifs at hne with hr
    · have hsup : (Finset.range (k (t + 1))).sup
          (fun c => bidCore k σ v none t (p * k (t + 1) + c)) ≤ (b0 : WithBot ℝ) := by
        apply Finset.sup_le
        intro c hc
        have h0 := hbest.2.2.2 c (Finset.mem_range.1 hc)
        rw [hb0, hj]
        split_ifs at h0
        · exact h0.le
        · exact h0
      have h2 := WithBot.coe_le_coe.1 (le_trans hr hsup)
      exact le_trans (hσ (t + 1) p (by omega) (by omega)).1 h2
    · exact absurd rfl hne

end AdInterm.SPE.L21A

open AdInterm.SPE AdInterm.SPE.L21A

theorem solution (n : ℕ) (k : ℕ → ℕ)
    (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t)
    (σ : Profile)
    (hσ : ∀ s i, 1 ≤ s → s ≤ n → IsMech (σ s i))
    (rS : ℝ) (hrS : 0 ≤ rS)
    (t j : ℕ) (ht : t ≤ n) (hj : j < nodes k n t) :
    ∃ T : (ℕ → ℝ) → WithTop ℝ,
      (∀ v v', (∀ i, ¬ DescendantBuyer k t j i → v i = v' i) → T v = T v') ∧
      (∀ v (b : ℝ), 0 ≤ b →
        (T v < (b : WithTop ℝ) → winsWith k n σ rS v t j b) ∧
        (winsWith k n σ rS v t j b → T v ≤ (b : WithTop ℝ))) ∧
      (∀ v, wins k n σ rS v t j → (pay k n σ rS v t j : WithTop ℝ) = T v) := by
  classical
  refine ⟨fun v => if h : ∃ b : ℝ, 0 ≤ b ∧ winsWith k n σ rS v t j b then
      ((sInf {b : ℝ | 0 ≤ b ∧ winsWith k n σ rS v t j b} : ℝ) : WithTop ℝ) else ⊤,
    ?_, ?_, ?_⟩
  · intro v v' hv
    have hiff : ∀ b : ℝ, winsWith k n σ rS v t j b ↔ winsWith k n σ rS v' t j b := by
      intro b
      unfold winsWith winnerAt
      rw [winnerDepth_congr (bidCore_indep t j b hv) _ le_rfl]
    simp only [hiff]
  · intro v b hb
    have hbdd : BddBelow {b : ℝ | 0 ≤ b ∧ winsWith k n σ rS v t j b} :=
      ⟨0, fun x hx => hx.1⟩
    constructor
    · intro hT
      by_cases h : ∃ b : ℝ, 0 ≤ b ∧ winsWith k n σ rS v t j b
      · dsimp only at hT
        rw [dif_pos h] at hT
        have hlt := WithTop.coe_lt_coe.1 hT
        obtain ⟨a, ha, hab⟩ := exists_lt_of_csInf_lt h hlt
        exact winsWith_upset hσ ht hab.le ha.2
      · dsimp only at hT
        rw [dif_neg h] at hT
        exact absurd hT (by simp)
    · intro hw
      have h : ∃ b : ℝ, 0 ≤ b ∧ winsWith k n σ rS v t j b := ⟨b, hb, hw⟩
      dsimp only
      rw [dif_pos h]
      exact WithTop.coe_le_coe.2 (csInf_le hbdd ⟨hb, hw⟩)
  · intro v hw
    obtain ⟨b0, hb0, hb0e⟩ := wins_report hσ hrS ht hw
    have hw0 : winsWith k n σ rS v t j b0 := by
      unfold winsWith winnerAt
      unfold wins winnerAt at hw
      rw [winnerDepth_congr (fun s _ => bidCore_selfEq t j b0 hb0e s) _ le_rfl]
      exact hw
    have h : ∃ b : ℝ, 0 ≤ b ∧ winsWith k n σ rS v t j b := ⟨b0, hb0, hw0⟩
    dsimp only
    rw [dif_pos h]
    rfl

