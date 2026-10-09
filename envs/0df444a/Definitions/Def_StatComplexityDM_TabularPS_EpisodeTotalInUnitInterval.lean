-- Prove2me | Definitions.Def_StatComplexityDM_TabularPS_EpisodeTotalInUnitInterval
-- name    : StatComplexityDM_TabularPS_EpisodeTotalInUnitInterval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:10.105966+00:00
-- url     : https://prove2.me/theorems/d74c7d0f-5aa9-4cfd-bb97-0a88310e4b00
-- title:
--   Appendix F.1 — almost-sure unit bound on cumulative episode reward
-- statement:
--   A model has bounded total episode reward if, under every randomized nonstationary policy, every trajectory with positive probability has total reward in $[0,1]$:
--   $$
--   0\le\sum_{h=1}^{H}r_h\le1\quad\text{almost surely}.
--   $$
--   This is the reward hypothesis of Lemmas F.2 and F.3 and Lemma 5.2. It permits individual rewards outside $[0,1]$ when their episode total remains bounded.
--
--   **Formalization Note** Positive probability is tested against the finite full trajectory law. The definition has no per reward range condition; §5.2's tabular proposition uses the separate shared `RewardsNormalized` condition.
-- source:
--   arXiv:2112.13487v3, Lemmas F.2–F.3, p. 107; Lemma 5.2, p. 33

import Mathlib
import Definitions.Def_StatComplexityDM_TabularPS_MDP

namespace StatComplexityDM.TabularPS

/-- The Appendix F hypothesis that cumulative episode reward is in `[0,1]`
almost surely under each randomized policy. Unlike the standing §5.2 tabular
convention, this does not restrict individual reward values. -/
def EpisodeTotalInUnitInterval {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W] {H : ℕ}
    (d1 : S → ℝ) (rv : W → ℝ) (M : TabMDP S A W H) : Prop :=
  ∀ π τ, IsPolicy π → trajLaw d1 M π τ ≠ 0 →
    0 ≤ ∑ h : Fin H, rv (τ h).2.2 ∧
      ∑ h : Fin H, rv (τ h).2.2 ≤ 1

end StatComplexityDM.TabularPS


