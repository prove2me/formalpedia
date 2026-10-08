-- Prove2me | Definitions.Def_WassersteinDRO_Regularization_nominalRisk_v2
-- name    : WassersteinDRO_Regularization_nominalRisk_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:36:01.20335+00:00
-- url     : https://prove2.me/theorems/e041de7a-fafb-4b97-8c24-74d03acbc2f3
-- title:
--   Nominal risk $R(Q,\ell)$ (extended-real, paper's convention)
-- statement:
--   The (nominal) risk of a loss function $\ell : E \to \mathbb{R}$ under a distribution $Q$ is $R(Q,\ell) = \mathbb{E}_Q[\ell(\xi)] \in [-\infty,\infty]$ (eq. (1)), the expectation taken with the paper's convention for non-integrable losses (p. 2; see `erealExpectation`): $+\infty$ if the positive part has infinite expectation, otherwise $\int \ell^+ dQ - \int \ell^- dQ$. For a $Q$-integrable $\ell$ it is the ordinary integral $\int \ell\,dQ$. It replaces the real-valued `nominalRisk`, whose Bochner integral returned the junk value $0$ for a non-integrable $\ell$. Redefined in this chapter's own namespace, mirroring `WassersteinDRO.Duality.nominalRisk` (v2).
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), eq. (1), p. 1, with the convention of p. 2

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_erealExpectation

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- The (nominal) risk of a loss function `ℓ` under a distribution `Q`, Kuhn et al. 2019,
eq. (1), p. 1: `R(Q,ℓ) = E_Q[ℓ(ξ)]`, taken with the paper's convention for non-integrable
losses (p. 2; see `erealExpectation`). Valued in `EReal`, so that `R(Q,ℓ)` is defined for
every measurable loss and every `Q`; for a `Q`-integrable `ℓ` it is the Bochner integral
`∫ ℓ dQ`. Replaces the retired real-valued `nominalRisk` (junk value `0` for non-integrable
`ℓ`). Redefined locally in this chapter's own namespace, mirroring
`WassersteinDRO.Duality.nominalRisk` (v2) verbatim. -/
noncomputable def nominalRisk {E : Type*} [MeasurableSpace E] (Q : Measure E) (ℓ : E → ℝ) :
    EReal :=
  erealExpectation Q (fun x => ((ℓ x : ℝ) : EReal))

end WassersteinDRO.Regularization


