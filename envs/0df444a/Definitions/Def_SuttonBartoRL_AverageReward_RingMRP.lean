-- Prove2me | Definitions.Def_SuttonBartoRL_AverageReward_RingMRP
-- name    : SuttonBartoRL_AverageReward_RingMRP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:40:16.255329+00:00
-- url     : https://prove2.me/theorems/2d2f0abf-3b73-49c9-b03d-1da75722417a
-- title:
--   The three-state ring Markov reward process of Exercise 10.7
-- statement:
--   The **ring Markov reward process** of Exercise 10.7 has three states $\mathsf A$, $\mathsf B$, $\mathsf C$ with deterministic transitions around the ring,
--   $$
--   \mathsf A \to \mathsf B \to \mathsf C \to \mathsf A,
--   $$
--   and a reward of $+1$ upon arrival in $\mathsf A$ (that is, on the transition $\mathsf C \to \mathsf A$) and $0$ otherwise. It is written as an MDP with a single action, taken with probability one by the only policy.
--
--   It is the book's example of a periodic Markov reward process whose differential values are computed with (10.13).
--
--   **Formalization Note** The states are `0`, `1`, `2` of `Fin 3` for $\mathsf A$, $\mathsf B$, $\mathsf C$, the successor of $s$ is $s + 1$ modulo 3, the action type is `Unit`, and the reward set is $\{0, 1\}$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 10.7, p. 251

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP

namespace SuttonBartoRL.AverageReward

open Classical in
/-- Exercise 10.7, p. 251: the ring Markov reward process. States `A = 0`, `B = 1`, `C = 2` of
`Fin 3`; a single (dummy) action, so the process is a Markov reward process; transitions go
deterministically around the ring `A → B → C → A` (`s ↦ s + 1` in `Fin 3`); a reward of `+1` is
received upon arrival in `A` and otherwise the reward is `0`. Reward set `{0, 1}`. -/
noncomputable def ringMRP : MDP (Fin 3) Unit where
  R := {0, 1}
  p s _ s' r := if s' = s + 1 then (if r = (if s' = 0 then 1 else 0) then 1 else 0) else 0
  p_nonneg s _ s' r := by split_ifs <;> norm_num
  p_sum s _ := by
    fin_cases s <;> simp

/-- The only policy of the ring MRP: the single action is taken with probability one. -/
def ringPolicy : SuttonBartoRL.FiniteMDP.Policy (Fin 3) Unit where
  prob _ _ := 1
  nonneg _ _ := zero_le_one
  sum_one _ := by simp

end SuttonBartoRL.AverageReward


