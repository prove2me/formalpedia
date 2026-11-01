-- Prove2me | Definitions.Def_BernoulliPoA_IsBNE
-- name    : BernoulliPoA_IsBNE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:44:07.721396+00:00
-- url     : https://prove2.me/theorems/53f5b79a-8459-4961-8f2e-d27c3b3e693a
-- title:
--   Bayes-Nash equilibrium
-- statement:
--   A strategy profile $\hat s$ is a **Bayes-Nash equilibrium** of the Bernoulli congestion game $\Gamma^{\mathbf p}$ when no player can lower the expected cost by a unilateral deviation:
--   $$
--   C_i(\hat s)\le C_i(s_i,\hat s_{-i})\qquad\text{for each } i\in\mathcal N\text{ and all } s_i\in\mathcal S_i.
--   $$
--   The set of these profiles is $\mathrm{NE}(\Gamma^{\mathbf p})$. Players choose their strategies before observing who is active.
--
--   **Formalization Note** A map from players to resource sets is not automatically a profile, so membership $\hat s_i\in\mathcal S_i$ is part of the definition.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Definition 1, p.13

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_expCost
open CongestionPoA.AsymSum

namespace BernoulliPoA

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- **Bayes-Nash equilibrium.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Definition 1, p.13: a strategy profile `ŝ` such that
`C_i(ŝ) ≤ C_i(s_i, ŝ_{-i})` for each player `i` and all `s_i ∈ S_i`. `NE(Γ^p)` is the set of these profiles.

**Formalization Note** A Lean map `ι → Finset E` is not automatically a profile, so `IsProfile G s` is part of the definition. -/
def IsBNE (G : CongestionGame ι E) (p : ι → ℝ) (s : ι → Finset E) : Prop :=
  IsProfile G s ∧ ∀ i, ∀ S ∈ G.strategies i, expCost G p s i ≤ expCost G p (Function.update s i S) i

end BernoulliPoA


