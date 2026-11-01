-- Prove2me | Definitions.Def_BernoulliPoA_weight
-- name    : BernoulliPoA_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:12.906599+00:00
-- url     : https://prove2.me/theorems/e78338c0-36eb-4471-bbd6-58ea529ffe9c
-- title:
--   Participation weight $p(\mathcal I)$
-- statement:
--   Let the players be active independently, player $j$ with probability $p_j$. For a set $\mathcal I$ of players,
--   $$
--   p(\mathcal I)=\prod_{j\in\mathcal I}p_j\prod_{j\notin\mathcal I}(1-p_j)
--   $$
--   is the probability that the set of active players is exactly $\mathcal I$.
--
--   Every expectation over the random participation in the mission is the finite sum with these weights.
--
--   **Formalization Note** The product runs over all players, so $p(\mathcal I)$ already contains the factor $p_i$ when $i\in\mathcal I$.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, §2.2, p.13

import Mathlib

namespace BernoulliPoA

/-- **Participation weight** `p(I) = ∏_{j ∈ I} p_j ∏_{j ∉ I} (1 - p_j)`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §2.2, p.13: the probability
that the set of active players is exactly `I` when each `j` is active independently with probability `p_j`.

**Formalization Note** The product runs over all players, so `weight p I` already contains the factor `p_i` for `i ∈ I`. -/
noncomputable def weight {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (I : Finset ι) : ℝ :=
  ∏ j, if j ∈ I then p j else 1 - p j

end BernoulliPoA


