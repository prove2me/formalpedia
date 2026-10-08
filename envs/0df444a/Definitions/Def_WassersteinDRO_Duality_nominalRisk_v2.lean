-- Prove2me | Definitions.Def_WassersteinDRO_Duality_nominalRisk_v2
-- name    : WassersteinDRO_Duality_nominalRisk_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:35:50.16776+00:00
-- url     : https://prove2.me/theorems/8cbd937f-5e2f-47e2-9f23-e672196842f6
-- title:
--   Nominal risk $R(Q,\ell)$ (extended-real, paper's convention)
-- statement:
--   The (nominal) risk of a loss function $\ell : E \to \mathbb{R}$ under a distribution $Q$ is $R(Q,\ell) = \mathbb{E}_Q[\ell(\xi)] \in [-\infty,\infty]$ (eq. (1)), the expectation taken with the paper's convention for non-integrable losses (p. 2; see `erealExpectation`): $+\infty$ if the positive part has infinite expectation, otherwise $\int \ell^+ dQ - \int \ell^- dQ$. For a $Q$-integrable $\ell$ it is the ordinary integral $\int \ell\,dQ$. It replaces the real-valued `nominalRisk`, whose Bochner integral returned the junk value $0$ for a non-integrable $\ell$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), eq. (1), p. 1, with the convention of p. 2

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The (nominal) risk of a loss function `ℓ` under a distribution `Q`, Kuhn et al. 2019,
eq. (1), p. 1: `R(Q,ℓ) = E_Q[ℓ(ξ)]`, the expectation of `ℓ` under `Q` taken with the paper's
own convention for non-integrable losses (p. 2: the expectation is `∞` whenever the positive
and negative parts both have infinite expectation; see `erealExpectation`). Valued in `EReal`,
so that `R(Q,ℓ)` is defined for every measurable loss and every `Q`, exactly as in the paper;
for a `Q`-integrable `ℓ` it is the ordinary Bochner integral `∫ ℓ dQ`. This replaces the
retired real-valued `nominalRisk`, whose Bochner integral silently returned `0` for a
non-integrable `ℓ`. -/
noncomputable def nominalRisk {E : Type*} [MeasurableSpace E] (Q : Measure E) (ℓ : E → ℝ) :
    EReal :=
  erealExpectation Q (fun x => ((ℓ x : ℝ) : EReal))

end WassersteinDRO.Duality


