-- Prove2me | Definitions.Def_FulfillFlex_meanDemand
-- name    : FulfillFlex_meanDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:16.229726+00:00
-- url     : https://prove2.me/theorems/79a60ee6-4485-4c1c-a185-4b6878b28840
-- title:
--   Expected daily demand $\mu_j$, finite mean and finite second moments
-- statement:
--   The daily demand vector $D^t=(D^t_0,\dots,D^t_N)$ has an arbitrary joint law $\nu$ on $\mathbb N^{N+1}$. The **expected daily demand** at DC $j$ is $\mu_j=\mathbb E[D^t_j]$. Demand has a **finite mean** if $\mathbb E[D^t_j]<\infty$ for every $j$, and **finite second moments** if $\mathbb E[(D^t_j)^2]<\infty$ for every $j$.
--
--   The mean enters the right side of the DLP (5). The second moment is what Lemma 7 needs when the proof of Proposition 3 applies it to total demand.
--
--   **Formalization Note** The law $\nu$ is a `PMF` on the countable type `DC N → ℕ`, so no law is excluded, and no independence across DCs is imposed. Both moments are computed in $[0,\infty]$; `meanDemand` converts to a real number, which is faithful because a finite second moment gives a finite mean.
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), §3.2, p.16 (μ_j); Lemma 7, p.49 (finite variance)

import Mathlib
import Definitions.Def_FulfillFlex_DC

open scoped ENNReal

namespace FulfillFlex

/-- **Expected daily demand `μ_j`.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), §3.2, p.16: "let µj be the expected
daily demand (i.e., µj = E[Dtj] for each t)".

**Formalization Note** `ν` is the joint law of the daily demand vector on `DC N → ℕ`; every law on
this countable type is a `PMF`, and no independence across DCs is imposed. The mean is computed
in `ℝ≥0∞` and converted to a real number. That conversion is faithful only when the mean is
finite, which `FiniteSecondMoment` guarantees. -/
noncomputable def meanDemand {N : ℕ} (ν : PMF (DC N → ℕ)) (j : DC N) : ℝ :=
  (∑' d, ν d * (d j : ℝ≥0∞)).toReal

/-- **Finite second moments of daily demand.**
`E[(D^t_j)²] < ∞` for every DC `j`. This is the hypothesis Lemma 7 of DeValve, Wei, Wu, Yuan,
SSRN 3265838 (2021-01-18 version), p.49, needs when the proof of Proposition 3 applies it to
`D_j(T)`. The paper never states it for the demand of its model.

**Formalization Note** Computed in `ℝ≥0∞`, so an infinite moment is the value `⊤` and not a junk
value. -/
def FiniteSecondMoment {N : ℕ} (ν : PMF (DC N → ℕ)) : Prop :=
  ∀ j, ∑' d, ν d * ((d j : ℝ≥0∞)) ^ 2 ≠ ⊤

/-- **Finite mean daily demand.**
`E[D^t_j] < ∞` for every DC `j`: the paper's `μ_j = E[D^t_j]`, DeValve, Wei, Wu, Yuan, SSRN 3265838
(2021-01-18 version), §3.2, p.16, is a real number. Implied by `FiniteSecondMoment`.

**Formalization Note** Computed in `ℝ≥0∞`, so an infinite mean is the value `⊤` and not a junk
value; under this hypothesis `meanDemand ν j` is the true mean. -/
def FiniteMean {N : ℕ} (ν : PMF (DC N → ℕ)) : Prop :=
  ∀ j, ∑' d, ν d * (d j : ℝ≥0∞) ≠ ⊤

end FulfillFlex


