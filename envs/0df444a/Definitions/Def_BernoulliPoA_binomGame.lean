-- Prove2me | Definitions.Def_BernoulliPoA_binomGame
-- name    : BernoulliPoA_binomGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:09.89814+00:00
-- url     : https://prove2.me/theorems/bfbdeccf-ddd6-4850-a176-4ea57d386fad
-- title:
--   The game $\Gamma_q$ with costs $c^q_e$
-- statement:
--   Given a congestion game $\Gamma$ with costs $(c_e)_{e\in\mathcal E}$ and $q\in(0,1]$, the game $\Gamma_q$ has the same players, resources and strategies, and the cost of each resource $e$ is the binomial expectation $c_e^q$.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Corollary 1, p.15

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_binomExp
open CongestionPoA.AsymSum

namespace BernoulliPoA

/-- **The game `Γ_q` with costs `c^q_e`.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Corollary 1, p.15: same players, resources and strategies as `G`,
with each cost `c_e` replaced by its binomial expectation `c^q_e`. -/
noncomputable def binomGame {ι E : Type*} (G : CongestionGame ι E) (q : ℝ) : CongestionGame ι E where
  strategies := G.strategies
  latency := fun e => binomExp (G.latency e) q

end BernoulliPoA


