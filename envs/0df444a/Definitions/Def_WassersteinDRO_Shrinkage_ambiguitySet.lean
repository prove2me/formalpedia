-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_ambiguitySet
-- name    : WassersteinDRO_Shrinkage_ambiguitySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:47:25.705862+00:00
-- url     : https://prove2.me/theorems/e7cad65a-3773-4b5b-b9e1-138a1c2bef81
-- title:
--   Wasserstein ambiguity set
-- statement:
--   The Wasserstein ambiguity set $B_{\varepsilon,p}(\hat P_N)$ of radius $\varepsilon$ around a
--   nominal distribution $\hat P_N$, supported on $\Xi$, is the set of probability measures $Q$ on
--   $\Xi$ with $W_p(Q,\hat P_N)\le\varepsilon$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, displayed equation, p. 6, just before eq. (6)

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_wassersteinDistance

open MeasureTheory

namespace WassersteinDRO.Shrinkage

/-- The Wasserstein ambiguity set, Kuhn et al. 2019, p. 6, displayed equation just before
eq. (6). Redefined locally in this chapter's own namespace; see
`Def_WassersteinDRO_Shrinkage_psdSqrt` for why. -/
def ambiguitySet {mx my : ℕ} (ε p : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin mx ⊕ Fin my)))
    (PN : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my))) :
    Set (Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my))) :=
  {Q | Q Set.univ = 1 ∧ Q Ξᶜ = 0 ∧ wassersteinDistance p Q PN ≤ ENNReal.ofReal ε}

end WassersteinDRO.Shrinkage


