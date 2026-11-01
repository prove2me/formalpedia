-- Prove2me | Definitions.Def_CoupledLearning_expectedUtility
-- name    : CoupledLearning_expectedUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:05.378015+00:00
-- url     : https://prove2.me/theorems/972c0bd9-cfca-4793-882e-cce94c4006bd
-- title:
--   Expected utility $\mathbb E_\theta[u_i^s(q)]=\sum_s\theta(s)u_i^s(q)$ in the game $G(\theta)$
-- statement:
--   Let $u_i^s(q)$ be player $i$'s average payoff at profile $q$ when the parameter is $s\in S$. For a belief $\theta=(\theta(s))_{s\in S}$, player $i$'s utility in the game $G(\theta)$ with static belief $\theta$ is the expected utility
--
--   $$\mathbb E_\theta[u_i^s(q)]=\sum_{s\in S}\theta(s)\,u_i^s(q).$$
--
--   It defines the equilibria $EQ(\theta)$ against which the strategy dynamics is measured.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, §2, p.8

import Mathlib
import Definitions.Def_CoupledLearning_Prof

namespace CoupledLearning

/-- Player `i`'s utility in the game `G(θ)` with a static belief `θ` (arXiv:2206.05637v2, §2,
p.8): the expected utility `E_θ[u_i^s(q)] = ∑_{s ∈ S} θ(s) u_i^s(q)`, where `u s i q` is player
`i`'s average payoff `u_i^s(q)` under parameter `s` at profile `q`. -/
noncomputable def expectedUtility {I S : Type*} [Fintype S] {d : I → ℕ}
    (u : S → I → Prof d → ℝ) (θ : S → ℝ) (i : I) (q : Prof d) : ℝ :=
  ∑ s, θ s * u s i q

end CoupledLearning


