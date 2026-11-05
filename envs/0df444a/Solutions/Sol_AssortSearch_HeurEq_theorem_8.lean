-- Prove2me | solution 1 for AssortSearch.HeurEq.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T01:02:28.960137+00:00
-- url     : https://prove2.me/submissions/287d6cac-6ae6-41eb-849d-b5a4e8dda84a

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model
import Theorems.Thm_AssortSearch_HeurEq_overestimate_narrower
import Theorems.Thm_AssortSearch_HeurEq_profit_agree_at_estimate

open RetailVariety.Structure AssortSearch.HeurEq

theorem solution {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hm : ∀ j k : Fin n, v k ≤ v j → m k ≤ m j)
    (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hcm : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0)
    (xstar xo : ℕ) (heq : IsHeuristicEquilibrium lam m c v v0 xstar)
    (hopt : IsOptimalDepth lam m c v v0 xo)
    (hdeeper : ∀ x : ℕ, xo < x → x ≤ n → trueProfit lam m c v v0 x < trueProfit lam m c v v0 xo) :
    xstar ≤ xo := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨h1, hn, hmax⟩ := heq
  -- π(x*) < π(x^o)
  have hlt' := hdeeper xstar hlt hn
  -- π(x*) = π(x* | v̂(x*))
  have hagree := profit_agree_at_estimate lam m c v v0 hv hv0 hlam xstar h1 hn
  -- π(x^o | v̂(x*)) ≤ π(x* | v̂(x*))
  have hle := hmax xo hopt.1
  -- π(x^o) ≤ π(x^o | v̂(x*))
  have hover : trueProfit lam m c v v0 xo ≤
      estProfit m c (estPref lam v v0 xstar) (estPrefNoPurchase lam v v0 xstar) xo := by
    rcases Nat.eq_zero_or_pos xo with h0 | hpos
    · subst h0
      have he : popularSet n 0 = ∅ := by
        ext j; simp [popularSet]
      simp [trueProfit, estProfit, he]
    · exact overestimate_narrower lam m c v v0 hv hanti hv0 hlam hm hcc hcm hc0 xstar
        ⟨h1, hn, hmax⟩ xo hpos hlt
  linarith
