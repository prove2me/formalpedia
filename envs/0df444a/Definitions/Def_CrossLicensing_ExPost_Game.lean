-- Prove2me | Definitions.Def_CrossLicensing_ExPost_Game
-- name    : CrossLicensing_ExPost_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:05.533576+00:00
-- url     : https://prove2.me/theorems/762175e9-cfe0-4ddb-bf4c-e22a0670fcb7
-- title:
--   Pure Nash equilibrium of a two-player real-strategy game
-- statement:
--   A two-player game specifies strategy sets $S_1,S_2\subseteq\mathbb R$ and payoffs $u_1(x_1,x_2)$ and $u_2(x_2,x_1)$, where each payoff lists the player's own action first. A profile $q=(q_1,q_2)$ is a **pure Nash equilibrium** when $q_i\in S_i$ and neither player can increase its payoff by changing only its own strategy:
--
--   $$
--   \begin{aligned}
--   u_1(x,q_2)&\le u_1(q_1,q_2)&&\text{for every }x\in S_1,\\
--   u_2(x,q_1)&\le u_2(q_2,q_1)&&\text{for every }x\in S_2.
--   \end{aligned}
--   $$
--
--   This general definition supplies the strategic condition for the paper's downstream quantity game.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. 10, equation (1) and the equilibrium leading to (2)

import Mathlib

namespace CrossLicensing.ExPost

/-- A pure Nash equilibrium of a two-player game with real strategies restricted to
sets `S₁` and `S₂`. The second payoff takes the second player's action first. -/
def IsNE (S₁ S₂ : Set ℝ) (u₁ u₂ : ℝ → ℝ → ℝ) (q : ℝ × ℝ) : Prop :=
  q.1 ∈ S₁ ∧ q.2 ∈ S₂ ∧
    (∀ x ∈ S₁, u₁ x q.2 ≤ u₁ q.1 q.2) ∧
    (∀ x ∈ S₂, u₂ x q.1 ≤ u₂ q.2 q.1)

end CrossLicensing.ExPost


