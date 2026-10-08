-- Prove2me | Definitions.Def_WassersteinDRO_Regularization_worstCaseRisk_v2
-- name    : WassersteinDRO_Regularization_worstCaseRisk_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:49:46.962296+00:00
-- url     : https://prove2.me/theorems/7ff7f03c-42e9-44b6-8edd-f296bda55dfc
-- title:
--   Worst-case risk $R_{\varepsilon,p}(\hat P_N,\ell)$ (paper's convention)
-- statement:
--   The worst-case risk of a loss $\ell$ over the type-$p$ Wasserstein ambiguity set of radius $\varepsilon$ around the nominal distribution $\hat P_N$ (eq. (6)): $$R_{\varepsilon,p}(\hat P_N,\ell) = \sup_{Q \in \mathcal{B}_{\varepsilon,p}(\hat P_N)} R(Q,\ell),$$ valued in $[-\infty,\infty]$, where $R(Q,\ell) = \mathbb{E}_Q[\ell(\xi)]$ is taken with the paper's convention for non-integrable losses (`nominalRisk`). The supremum is a genuine least upper bound: $+\infty$ for an unbounded family and $-\infty = \sup\emptyset$ for an empty ball. It replaces the `worstCaseRisk` that discarded every $Q$ under which $\ell$ is not integrable instead of assigning it the paper's value $\mathbb{E}_Q[\ell] \in \{-\infty,+\infty\}$. Redefined in this chapter's own namespace, mirroring `WassersteinDRO.Duality.worstCaseRisk` (v2).
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), eq. (6), p. 6

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_ambiguitySet
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk_v2

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- The worst-case risk, Kuhn et al. 2019, p. 6, eq. (6):
`Rε,p(PN,ℓ) = sup_{Q ∈ Bε,p(PN)} R(Q,ℓ)`, the supremum over the Wasserstein ambiguity set of
the risk `R(Q,ℓ) = E_Q[ℓ(ξ)]` taken with the paper's convention for non-integrable losses
(`nominalRisk`). Valued in `EReal` (genuine supremum, `+∞` if unbounded, `-∞` if the ball is
empty). Replaces the retired `worstCaseRisk`, which dropped every `Q` under which `ℓ` is not
integrable instead of assigning it the paper's value `E_Q[ℓ] ∈ {-∞,+∞}`. Redefined locally in
this chapter's own namespace, mirroring `WassersteinDRO.Duality.worstCaseRisk` (v2). -/
noncomputable def worstCaseRisk {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (Ξ : Set E) (PN : Measure E) (ℓ : E → ℝ) : EReal :=
  ⨆ (Q : Measure E) (_ : Q ∈ ambiguitySet ε p Ξ PN), nominalRisk Q ℓ

end WassersteinDRO.Regularization


