-- Prove2me | Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2
-- name    : WassersteinDRO_Duality_worstCaseRisk_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:49:27.837452+00:00
-- url     : https://prove2.me/theorems/ddff5b3b-cf42-44a2-ba8d-92f284bec538
-- title:
--   Worst-case risk $R_{\varepsilon,p}(\hat P_N,\ell)$ (paper's convention)
-- statement:
--   The worst-case risk of a loss $\ell$ over the type-$p$ Wasserstein ambiguity set of radius $\varepsilon$ around the nominal distribution $\hat P_N$ (eq. (6)): $$R_{\varepsilon,p}(\hat P_N,\ell) = \sup_{Q \in \mathcal{B}_{\varepsilon,p}(\hat P_N)} R(Q,\ell),$$ valued in $[-\infty,\infty]$, where $R(Q,\ell) = \mathbb{E}_Q[\ell(\xi)]$ is taken with the paper's convention for non-integrable losses (`nominalRisk`). The supremum is a genuine least upper bound: $+\infty$ for an unbounded family and $-\infty = \sup\emptyset$ for an empty ball. It replaces the `worstCaseRisk` that discarded every $Q$ under which $\ell$ is not integrable instead of assigning it the paper's value $\mathbb{E}_Q[\ell] \in \{-\infty,+\infty\}$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), eq. (6), p. 6

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_ambiguitySet
import Definitions.Def_WassersteinDRO_Duality_nominalRisk_v2

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The worst-case risk, Kuhn et al. 2019, p. 6, eq. (6):
`Rε,p(PN,ℓ) = sup_{Q ∈ Bε,p(PN)} R(Q,ℓ)`, the supremum of the risk `R(Q,ℓ) = E_Q[ℓ(ξ)]` over
the Wasserstein ambiguity set `Bε,p(PN)`. Valued in `EReal`: the supremum is a genuine least
upper bound (`+∞` for an unbounded family, `-∞ = sup ∅` for an empty ball), and each term is
the paper's `R(Q,ℓ)` with its convention for non-integrable losses (`nominalRisk`). This
replaces the retired `worstCaseRisk`, which dropped every `Q` under which `ℓ` is not
integrable (an `Integrable ℓ Q` guard); the paper instead assigns such `Q` the value
`E_Q[ℓ] ∈ {-∞, +∞}` (p. 2) and keeps them in the supremum. -/
noncomputable def worstCaseRisk {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (Ξ : Set E) (PN : Measure E) (ℓ : E → ℝ) : EReal :=
  ⨆ (Q : Measure E) (_ : Q ∈ ambiguitySet ε p Ξ PN), nominalRisk Q ℓ

end WassersteinDRO.Duality


