-- Prove2me | Definitions.Def_AltRegret_Supplement_IsHarmonicAdversary
-- name    : AltRegret_Supplement_IsHarmonicAdversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:10:05.623502+00:00
-- url     : https://prove2.me/theorems/52257f38-351d-47e7-ac75-b73232473b29
-- title:
--   Adaptive largest-surviving-coordinate adversary
-- statement:
--   Starting from $S_0=[d]$, on round $1\le t\le d-1$ the adversary observes the current simplex action $x_t$, removes a coordinate $j_t\in\arg\max_{j\in S_{t-1}}x_{t,j}$, and assigns cost $-1$ to the surviving coordinates and $+1$ to all removed coordinates. From round $d$ onward it repeats $c_{d-1}$.
--
--   The predicate records the surviving sets, maximizing coordinates, updates, and costs, so the dependence on the currently observed action—and the absence of dependence on future actions—is explicit.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, proof of Theorem 6, p.9

import Mathlib
import Definitions.Def_AltRegret_altRegretAgainst

namespace AltRegret.Supplement

/-- The adaptive adversary used in Theorem 6: after seeing `x_t`, it removes a largest-mass
surviving coordinate and assigns `-1` to survivors and `+1` to removed coordinates. -/
def IsHarmonicAdversary {d : ℕ} (x : ℕ → Fin d → ℝ) (c : ℕ → Fin d → ℝ) : Prop :=
  ∃ (S : ℕ → Finset (Fin d)) (j : ℕ → Fin d),
    S 0 = Finset.univ ∧
    (∀ t, 1 ≤ t → t ≤ d - 1 →
      j t ∈ S (t - 1) ∧
      (∀ i ∈ S (t - 1), x t i ≤ x t (j t)) ∧
      S t = (S (t - 1)).erase (j t) ∧
      ∀ i, c t i = if i ∈ S t then -1 else 1) ∧
    (∀ t, d ≤ t → c t = c (d - 1))

end AltRegret.Supplement


