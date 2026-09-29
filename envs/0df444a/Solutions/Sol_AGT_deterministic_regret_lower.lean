-- Prove2me | solution 1 for AGT.deterministic_regret_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-12T16:36:23.1572+00:00
-- url     : https://prove2.me/submissions/57c2b50a-9411-49b5-8b00-78fd48db0af7

import Definitions.Def_agt_regret

namespace AGT

open Finset

section Adversary

variable {n : ℕ}

/-- The adversary's history against a deterministic algorithm `D`: at each
step it charges loss `1` to the action `D` is about to play and `0` to every
other action.  Recursion on the length of the history is what makes the
construction well founded: the loss vector revealed at time `t` is built
from the first `t` loss vectors only. -/
def advHist (D : List (Fin (n + 1) → ℝ) → Fin (n + 1)) :
    ℕ → List (Fin (n + 1) → ℝ)
  | 0 => []
  | t + 1 => advHist D t ++ [fun i => if D (advHist D t) = i then 1 else 0]

/-- The loss vector the adversary reveals at time `t`. -/
def advLoss (D : List (Fin (n + 1) → ℝ) → Fin (n + 1)) (t : ℕ)
    (i : Fin (n + 1)) : ℝ :=
  if D (advHist D t) = i then 1 else 0

/-- The history the algorithm actually observes at time `t` is the one the
adversary has built. -/
theorem map_range_advLoss (D : List (Fin (n + 1) → ℝ) → Fin (n + 1)) (t : ℕ) :
    (List.range t).map (advLoss D) = advHist D t := by
  induction t with
  | zero => simp [advHist]
  | succ t ih =>
      rw [List.range_succ, List.map_append, ih]
      rfl

/-- Consequently the deterministic play at time `t` is `D (advHist D t)`. -/
theorem detPlay_advLoss (D : List (Fin (n + 1) → ℝ) → Fin (n + 1)) (t : ℕ) :
    detPlay D (advLoss D) t = D (advHist D t) := by
  rw [detPlay, map_range_advLoss]

end Adversary

end AGT

open AGT Finset in
theorem solution {n : ℕ}
    (D : List (Fin (n + 1) → ℝ) → Fin (n + 1)) :
    ∃ ℓ : ℕ → Fin (n + 1) → ℝ,
      (∀ t i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      (∀ T : ℕ, ∑ t ∈ Finset.range T, ℓ t (detPlay D ℓ t) = T) ∧
      (∀ T : ℕ, ∃ k : Fin (n + 1), actionLoss ℓ k T ≤ ((T / (n + 1) : ℕ) : ℝ)) := by
  classical
  refine ⟨advLoss D, ?_, ?_, ?_⟩
  · intro t i
    by_cases h : D (advHist D t) = i
    · exact Or.inr (by simp [advLoss, h])
    · exact Or.inl (by simp [advLoss, h])
  · intro T
    have : ∀ t ∈ Finset.range T, advLoss D t (detPlay D (advLoss D) t) = 1 := by
      intro t _
      rw [detPlay_advLoss]
      simp [advLoss]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  · intro T
    -- The benchmark of an action is the number of times `D` selected it.
    have hAL : ∀ k : Fin (n + 1), actionLoss (advLoss D) k T =
        (((Finset.range T).filter (fun t => D (advHist D t) = k)).card : ℝ) := by
      intro k
      rw [actionLoss]
      simp only [advLoss, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        mul_one]
    -- The fibres of the selection map partition the first `T` steps.
    have hcard : (Finset.range T).card =
        ∑ k : Fin (n + 1),
          ((Finset.range T).filter (fun t => D (advHist D t) = k)).card :=
      Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
    rw [Finset.card_range] at hcard
    -- Pigeonhole on the fibres.
    have hnat : ∃ k : Fin (n + 1),
        ((Finset.range T).filter (fun t => D (advHist D t) = k)).card ≤ T / (n + 1) := by
      by_contra hc
      push Not at hc
      have hge : ∑ _k : Fin (n + 1), (T / (n + 1) + 1) ≤
          ∑ k : Fin (n + 1),
            ((Finset.range T).filter (fun t => D (advHist D t) = k)).card :=
        Finset.sum_le_sum fun k _ => Nat.succ_le_of_lt (hc k)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        ← hcard] at hge
      have hexp : (n + 1) * (T / (n + 1) + 1)
          = (n + 1) * (T / (n + 1)) + (n + 1) := by ring
      rw [hexp] at hge
      have h1 := Nat.div_add_mod T (n + 1)
      have h2 : T % (n + 1) < n + 1 := Nat.mod_lt _ (Nat.succ_pos n)
      omega
    obtain ⟨k, hk⟩ := hnat
    exact ⟨k, by rw [hAL k]; exact_mod_cast hk⟩
