-- Prove2me | Definitions.Def_WassersteinDRO_Regularization_ambiguitySet
-- name    : WassersteinDRO_Regularization_ambiguitySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:38:37.728875+00:00
-- url     : https://prove2.me/theorems/63297e50-cf22-45fa-87a5-5617788710a2
-- title:
--   Wasserstein ambiguity set
-- statement:
--   The Wasserstein ambiguity set $B_{\varepsilon,p}(\hat P_N)$ of radius $\varepsilon$ around a
--   nominal distribution $\hat P_N$, supported on $\Xi$, is the set of probability measures $Q$ on
--   $\Xi$ with $W_p(Q,\hat P_N) \le \varepsilon$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, displayed equation, p. 6, just before eq. (6)

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_wassersteinDistance

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- The Wasserstein ambiguity set, Kuhn et al. 2019, p. 6, displayed equation just before
eq. (6). Redefined locally in this chapter's own namespace; see
`Def_WassersteinDRO_Regularization_wassersteinDistance` for why. -/
def ambiguitySet {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (Ξ : Set E) (PN : Measure E) : Set (Measure E) :=
  {Q | Q Set.univ = 1 ∧ Q Ξᶜ = 0 ∧ wassersteinDistance p Q PN ≤ ENNReal.ofReal ε}

end WassersteinDRO.Regularization


