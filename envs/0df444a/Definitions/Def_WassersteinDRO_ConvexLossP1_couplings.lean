-- Prove2me | Definitions.Def_WassersteinDRO_ConvexLossP1_couplings
-- name    : WassersteinDRO_ConvexLossP1_couplings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:48:09.803138+00:00
-- url     : https://prove2.me/theorems/89f09860-e33b-490c-85aa-d017b3b11f19
-- title:
--   Couplings $\Pi(\mathbb Q, \mathbb Q')$
-- statement:
--   Let $\mathbb Q$ and $\mathbb Q'$ be measures on a measurable space $E$. The set of **couplings** $\Pi(\mathbb Q, \mathbb Q')$ is the set of all probability measures $\pi$ on $E \times E$ whose marginals are $\mathbb Q$ and $\mathbb Q'$:
--   $$\pi(A \times E) = \mathbb Q(A), \qquad \pi(E \times B) = \mathbb Q'(B)$$
--   for all measurable $A, B \subseteq E$.
--
--   Couplings are the transportation plans in the definition of the Wasserstein distance: $\pi(A \times B)$ is the mass moved from $A$ to $B$.
--
--   **Formalization Note** The marginal conditions are stated as equalities of push-forward measures under the two coordinate projections. When $\mathbb Q$ and $\mathbb Q'$ are probability measures the set is nonempty (it contains the product measure).
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Definition 1, p. 3 (Π(Q, Q′))

import Mathlib

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **The set `Π(Q, Q')` of couplings.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Definition 1, p. 3: "Π(Q, Q′) denotes the set of all joint probability distributions of
ξ ∈ R^m and ξ′ ∈ R^m with marginals Q and Q′, respectively."

`couplings Q Q'` is the set of probability measures `π` on `E × E` whose first marginal is `Q` and
whose second marginal is `Q'`.

**Formalization Note.** The marginals are the push-forwards under the (measurable) projections
`Prod.fst` and `Prod.snd`. The set is nonempty whenever `Q` and `Q'` are probability measures
(the product measure belongs to it). -/
def couplings {E : Type*} [MeasurableSpace E] (Q Q' : Measure E) : Set (Measure (E × E)) :=
  {π | IsProbabilityMeasure π ∧ π.map Prod.fst = Q ∧ π.map Prod.snd = Q'}

end WassersteinDRO.ConvexLossP1


