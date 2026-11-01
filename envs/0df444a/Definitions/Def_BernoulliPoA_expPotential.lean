-- Prove2me | Definitions.Def_BernoulliPoA_expPotential
-- name    : BernoulliPoA_expPotential
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:06.817221+00:00
-- url     : https://prove2.me/theorems/436fdb98-41a1-42a5-a314-31019520c582
-- title:
--   Expected Rosenthal potential $\Phi(s)$
-- statement:
--   The **expected Rosenthal potential** of a profile $s$ is
--   $$
--   \Phi(s)=\sum_{\mathcal I}p(\mathcal I)\sum_{e}\sum_{k=1}^{n^{\mathcal I}_e(s)}c_e(k),
--   $$
--   the expectation of Rosenthal's potential of the realized game.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, proof of Proposition 1, display (16), p.14

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_weight
import Definitions.Def_BernoulliPoA_restrict
open CongestionPoA.AsymSum

namespace BernoulliPoA

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- **Expected Rosenthal potential** `Φ(s)`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, proof of Proposition 1, display (16), p.14:
`Φ(s) = E[∑_e ∑_{k=1}^{N_e(s)} c_e(k)]`, the expectation being the finite sum over the realized set `I` with weights `p(I)`. -/
noncomputable def expPotential (G : CongestionGame ι E) (p : ι → ℝ) (s : ι → Finset E) : ℝ :=
  ∑ I : Finset ι, weight p I * ∑ e, ∑ k ∈ Finset.Icc 1 (load (restrict s I) e), G.latency e k

end BernoulliPoA


