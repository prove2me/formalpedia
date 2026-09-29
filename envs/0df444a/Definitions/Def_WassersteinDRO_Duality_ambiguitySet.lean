-- Prove2me | Definitions.Def_WassersteinDRO_Duality_ambiguitySet
-- name    : WassersteinDRO_Duality_ambiguitySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:15:50.432882+00:00
-- url     : https://prove2.me/theorems/e7b9c567-d030-4514-bd9a-a82f196f53a9
-- title:
--   Wasserstein ambiguity set
-- statement:
--   The Wasserstein ambiguity set of radius $\varepsilon \ge 0$ around a nominal distribution
--   $P_N$ (with respect to the type-$p$ Wasserstein distance), restricted to probability
--   measures supported on a closed set $\Xi \subseteq E$, is
--   $$B_{\varepsilon,p}(P_N) = \{Q \in \mathcal{P}(\Xi) : W_p(Q,P_N) \le \varepsilon\}.$$
--   "Supported on $\Xi$" is formalized as $Q$ assigning zero mass to the complement of
--   $\Xi$.
-- source:
--   Kuhn et al. 2019, p. 6, displayed equation immediately preceding eq. (6)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The Wasserstein ambiguity set, Kuhn et al. 2019, p. 6, displayed equation just before
eq. (6): `Bε,p(PN) = {Q ∈ P(Ξ) : Wp(Q,PN) ≤ ε}`, the ball of radius `ε ≥ 0` around the
nominal distribution `PN` in the type-`p` Wasserstein distance, restricted to probability
measures supported on the closed set `Ξ`. "Supported on `Ξ`" is encoded as `Q Ξᶜ = 0`
(the complement is `Q`-null), the standard measure-theoretic reading of `Q ∈ P(Ξ)`. -/
def ambiguitySet {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (Ξ : Set E) (PN : Measure E) : Set (Measure E) :=
  {Q | Q Set.univ = 1 ∧ Q Ξᶜ = 0 ∧ wassersteinDistance p Q PN ≤ ENNReal.ofReal ε}

end WassersteinDRO.Duality


