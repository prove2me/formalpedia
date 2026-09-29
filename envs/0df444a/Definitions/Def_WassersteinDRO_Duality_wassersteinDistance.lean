-- Prove2me | Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
-- name    : WassersteinDRO_Duality_wassersteinDistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:14:30.174625+00:00
-- url     : https://prove2.me/theorems/230c1449-51f2-4622-83e8-2427508cbdbb
-- title:
--   Type-$p$ Wasserstein distance
-- statement:
--   For $p \in [1,\infty)$, the type-$p$ Wasserstein distance between two Borel probability
--   measures $Q, Q'$ on $E$ (representing $\mathbb{R}^m$ equipped with an arbitrary fixed
--   norm) is
--   $$W_p(Q,Q') = \left(\inf_{\pi \in \Pi(Q,Q')} \int_{E\times E} \|\xi-\xi'\|^p\, \pi(d\xi,d\xi')\right)^{1/p},$$
--   where $\Pi(Q,Q')$ is the set of couplings of $Q$ and $Q'$: joint probability measures on
--   $E \times E$ whose two marginals (pushforwards under the coordinate projections) are $Q$
--   and $Q'$ respectively. The infimum is taken over $\pi$ satisfying the coupling condition;
--   it is $+\infty$ (recorded as the top element of $[0,\infty]$) if no coupling exists.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, INFORMS TutORials 2019, DOI 10.1287/educ.2019.0198, Definition 1, p. 3, eq. (5)

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The type-`p` Wasserstein distance between two Borel probability measures `Q`, `Q'` on `E`
(representing `ℝ^m` with an arbitrary fixed norm), Kuhn–Mohajerin Esfahani–Nguyen–
Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization*, INFORMS TutORials
2019, Definition 1, p. 3, eq. (5):

`Wp(Q,Q') = (inf_{π ∈ Π(Q,Q')} ∫ ‖ξ-ξ'‖^p π(dξ,dξ'))^{1/p}`,

where `Π(Q,Q')` is the set of couplings of `Q` and `Q'`: joint measures on `E × E` whose two
marginals (pushforwards under the coordinate projections) are `Q` and `Q'`. The infimum over
the constrained set of couplings is encoded as an infimum guarded by the coupling condition,
which defaults to `⊤` outside the feasible set — the standard Mathlib idiom for a constrained
extremum, not a junk value, since it correctly represents "no such π" as "no finite cost". -/
noncomputable def wassersteinDistance {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (p : ℝ) (Q Q' : Measure E) : ENNReal :=
  (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q'),
      ∫⁻ x : E × E, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π) ^ (1 / p)

end WassersteinDRO.Duality


