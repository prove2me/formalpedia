-- Prove2me | Definitions.Def_BernoulliPoA_prophetCost
-- name    : BernoulliPoA_prophetCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:14.567766+00:00
-- url     : https://prove2.me/theorems/a33bd1d6-56f1-41a1-bf7d-c6b2e482899b
-- title:
--   Expected prophet optimal cost $C_{\mathsf{pr}}$
-- statement:
--   The prophet observes the realized set $\mathcal I$ and selects a profile minimizing the realized social cost:
--   $$
--   C_{\mathsf{pr}}(\mathcal I)=\min_{s\in\mathcal S}\sum_{e}n^{\mathcal I}_e(s)\,c_e\bigl(n^{\mathcal I}_e(s)\bigr),\qquad
--   C_{\mathsf{pr}}=\sum_{\mathcal I}p(\mathcal I)\,C_{\mathsf{pr}}(\mathcal I).
--   $$
--
--   This is the benchmark of the prophet price of anarchy.
--
--   **Formalization Note** The value lies in $[0,\infty]$, since the price of anarchy divides by it. On the games of the mission the conversion from the reals loses nothing, and the infimum over the finitely many profiles is the minimum.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, displays (24)–(25), p.16

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_weight
import Definitions.Def_BernoulliPoA_restrict
open CongestionPoA.AsymSum
open scoped ENNReal

namespace BernoulliPoA

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- **Expected prophet optimal cost** `C_pr`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §3, displays (24)–(25), p.16: for each realized set `I` the planner
minimizes `∑_e n^I_e(s) c_e(n^I_e(s))` over the strategy profiles `s ∈ S`, and `C_pr = ∑_I p(I) C_pr(I)`.

**Formalization Note** The value lies in `ℝ≥0∞`, because `PPoA` divides by it. For a game whose costs are nonnegative at loads
`≥ 1` and with `0 ≤ p_j ≤ 1`, `ENNReal.ofReal` loses nothing. Every strategy set being nonempty, the infimum runs over a
finite nonempty set of profiles and is the minimum of (24). -/
noncomputable def prophetCost (G : CongestionGame ι E) (p : ι → ℝ) : ℝ≥0∞ :=
  ∑ I : Finset ι, ENNReal.ofReal (weight p I) *
    ⨅ s : ι → Finset E, ⨅ _ : IsProfile G s, ENNReal.ofReal (sumCost G (restrict s I))

end BernoulliPoA


