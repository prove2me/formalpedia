-- Prove2me | Definitions.Def_BernoulliPoA_PPoA
-- name    : BernoulliPoA_PPoA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:45:07.687308+00:00
-- url     : https://prove2.me/theorems/3b4304b7-1d80-4818-89df-51010f4b1f8b
-- title:
--   Prophet price of anarchy $\mathsf{PPoA}(\Gamma^{\mathbf p})$
-- statement:
--   The **prophet price of anarchy** of a Bernoulli congestion game compares the worst equilibrium with the prophet:
--   $$
--   \mathsf{PPoA}(\Gamma^{\mathbf p})=\max_{s\in\mathrm{NE}(\Gamma^{\mathbf p})}\frac{C(s)}{C_{\mathsf{pr}}}.
--   $$
--
--   **Formalization Note** The ratio is taken in $[0,\infty]$ with $x/0=\infty$ for $x>0$ and $0/0=0$. The first value is the one the paper uses in Case 1 of the proof of Theorem 3. The source fixes no value for the second, and the goal theorem records this reading. Equilibria exist by Proposition 1, and the supremum over the finitely many profiles is a maximum.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, display (26), p.16

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_expSocialCost
import Definitions.Def_BernoulliPoA_IsBNE
import Definitions.Def_BernoulliPoA_prophetCost
open CongestionPoA.AsymSum
open scoped ENNReal

namespace BernoulliPoA

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- **Prophet price of anarchy** `PPoA(Γ^p)`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §3, display (26), p.16: `PPoA(Γ^p) = max_{s ∈ NE(Γ^p)} C(s) / C_pr`.

**Formalization Note** The ratio is taken in `ℝ≥0∞`: `x / 0 = ⊤` for `x > 0`, which is the value `PPoA(Γ^p) = ∞` of Case 1 of
the proof of Theorem 3 (p.ec3), and `0 / 0 = 0`. The paper fixes no value of `0 / 0` in (26); see the goal `theorem_3` for this
reading. `NE(Γ^p)` is nonempty by Proposition 1, so the supremum is not over the empty set, and it is a maximum because
there are finitely many profiles. -/
noncomputable def PPoA (G : CongestionGame ι E) (p : ι → ℝ) : ℝ≥0∞ :=
  ⨆ s : ι → Finset E, ⨆ _ : IsBNE G p s, ENNReal.ofReal (expSocialCost G p s) / prophetCost G p

end BernoulliPoA


