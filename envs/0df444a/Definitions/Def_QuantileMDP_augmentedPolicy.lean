-- Prove2me | Definitions.Def_QuantileMDP_augmentedPolicy
-- name    : QuantileMDP_augmentedPolicy
-- status  : Definition
-- author  : @shuffle
-- created : 2026-11-14T01:38:42.009444+00:00
-- url     : https://prove2.me/theorems/cf077081-0f56-40a3-b661-efce17f195e7
-- title:
--   Quantile MDP augmented-state policy and its level update
-- statement:
--   An action map and a successor-dependent quantile-level update induce a deterministic history-dependent policy. The level is initialized at the starting time and then updated once for each observed transition. The action depends only on time, the current state, and the current level.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.3, Theorem 3, pp. 13–14. https://arxiv.org/abs/1711.05788v5

import Mathlib.Data.Fin.Tuple.Basic
import Definitions.Def_QuantileMDP_Model

namespace QuantileMDP

/-- The current quantile level after processing a history, starting at time `t`
with level `τ`. The update uses the old state, old level, and observed successor. -/
def policyLevel {S : Type*} (next : ℕ → S → ℝ → S → ℝ) :
    (k : ℕ) → ℕ → ℝ → (Fin (k + 1) → S) → ℝ
  | 0, _, τ, _ => τ
  | k + 1, t, τ, h => policyLevel next k (t + 1) (next t (h 0) τ (h 1)) (Fin.tail h)

/-- The history-dependent policy induced by an action and level update on the
augmented state. Time `t` is the starting time and `τ` the initial level. -/
def augmentedPolicy {S A : Type*} (act : ℕ → S → ℝ → A) (next : ℕ → S → ℝ → S → ℝ)
    (t : ℕ) (τ : ℝ) : Policy S A :=
  fun k h => act (t + k) (h (Fin.last k)) (policyLevel next k t τ h)

end QuantileMDP


