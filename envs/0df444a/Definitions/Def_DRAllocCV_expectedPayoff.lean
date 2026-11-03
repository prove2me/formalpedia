-- Prove2me | Definitions.Def_DRAllocCV_expectedPayoff
-- name    : DRAllocCV_expectedPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:47.966354+00:00
-- url     : https://prove2.me/theorems/d62c3f14-5007-44dd-b812-80365b6abb99
-- title:
--   Expected payoff $\mathbb E_{\mathbb P}[\sum_i(p_i(\tilde t)\tilde t_i-q_i(\tilde t)c_i)]$
-- statement:
--   For a distribution $\mathbb P$ of the random type profile $\tilde t$, the **expected payoff** of the mechanism $(p,q)$ is
--
--   $$
--   \mathbb E_{\mathbb P}\Bigl[\sum_{i\in\mathcal I}\bigl(p_i(\tilde t)\,\tilde t_i-q_i(\tilde t)\,c_i\bigr)\Bigr].
--   $$
--
--   The principal maximizes the worst case of this quantity over the ambiguity set (problem (MDP)), and Pareto robust dominance compares it distribution by distribution (inequality (1)).
--
--   **Formalization Note** The expectation is the Lebesgue (Bochner) integral over $\mathbb R^I$. The theorems apply it only to probability measures concentrated on $\mathcal T$ and feasible mechanisms, for which the integrand is measurable and bounded almost surely, so the integral is the genuine expectation.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.7, (MDP) and (1)

import Mathlib
import Definitions.Def_DRAllocCV_payoff

open MeasureTheory

namespace DRAllocCV

/-- The **expected payoff** `𝔼_ℙ[∑ᵢ (pᵢ(t̃) t̃ᵢ − qᵢ(t̃) cᵢ)]` of the mechanism `(p, q)` under the
type distribution `ℙ` (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.7, (MDP) and (1)).

**Formalization Note.** The expectation is the Bochner integral over `ι → ℝ`. Every statement
that uses it takes `ℙ` to be a probability measure with `ℙ(𝒯ᶜ) = 0` and `(p, q)` feasible, so the
integrand is measurable and bounded on a set of full measure and the integral is the genuine
expectation (never the junk value `0` of a non-integrable function). -/
noncomputable def expectedPayoff {ι : Type*} [Fintype ι] (P : Measure (ι → ℝ)) (c : ι → ℝ)
    (p q : ι → (ι → ℝ) → ℝ) : ℝ :=
  ∫ t, payoff c p q t ∂P

end DRAllocCV


