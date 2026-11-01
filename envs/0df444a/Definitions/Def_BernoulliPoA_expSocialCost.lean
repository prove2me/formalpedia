-- Prove2me | Definitions.Def_BernoulliPoA_expSocialCost
-- name    : BernoulliPoA_expSocialCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:06.138679+00:00
-- url     : https://prove2.me/theorems/7e0ccf62-b3bc-4367-99d5-8e26d3339206
-- title:
--   Expected social cost $C(s)$
-- statement:
--   The **expected social cost** of a profile $s$ is
--   $$
--   C(s)=\sum_{\mathcal I}p(\mathcal I)\sum_{e}n^{\mathcal I}_e(s)\,c_e\bigl(n^{\mathcal I}_e(s)\bigr),
--   $$
--   the expected total cost of the active players. It equals $\sum_i C_i(s)$.
--
--   **Formalization Note** The inner sum is the deterministic social cost of the profile of the active players.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, displays (14), p.13, and (21), p.15

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_weight
import Definitions.Def_BernoulliPoA_restrict
open CongestionPoA.AsymSum

namespace BernoulliPoA

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- **Expected social cost** `C(s)`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §2.2, display (14), p.13, and §3, display (21), p.15:
`C(s) = E[∑_e n^I_e(s) c_e(n^I_e(s))]`, the expectation being the finite sum over the realized set `I` with weights `p(I)`.

**Formalization Note** `sumCost G (restrict s I)` is `∑_i ∑_{e ∈ s_i, i ∈ I} c_e(n^I_e(s)) = ∑_e n^I_e(s) c_e(n^I_e(s))`.
The equality `C(s) = ∑_i C_i(s)` of (21) is checked in `Solutions/verification/BernoulliPoA_sanity.lean`. -/
noncomputable def expSocialCost (G : CongestionGame ι E) (p : ι → ℝ) (s : ι → Finset E) : ℝ :=
  ∑ I : Finset ι, weight p I * sumCost G (restrict s I)

end BernoulliPoA


