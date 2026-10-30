-- Prove2me | Definitions.Def_WassersteinDRO_ConvexLossP1_ambiguityBall
-- name    : WassersteinDRO_ConvexLossP1_ambiguityBall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:49:29.255722+00:00
-- url     : https://prove2.me/theorems/46c919e1-d91e-43b3-bc7a-6066739494dd
-- title:
--   Wasserstein ambiguity set $\mathbb B_{\varepsilon,p}(\mathbb P)$
-- statement:
--   Let $(E, \|\cdot\|)$ be a normed space with its Borel $\sigma$-algebra, $\Xi \subseteq E$, $\varepsilon \in \mathbb R$, $p \ge 1$, and let $\mathbb P$ be a measure on $E$ (the nominal distribution). The **Wasserstein ambiguity set** is
--   $$\mathbb B_{\varepsilon,p}(\mathbb P) = \{\mathbb Q \in \mathcal P(\Xi) : W_p(\mathbb Q, \mathbb P) \le \varepsilon\},$$
--   where $\mathcal P(\Xi)$ is the family of all probability distributions supported on $\Xi$, i.e. Borel probability measures $\mathbb Q$ on $E$ with $\mathbb Q(E \setminus \Xi) = 0$.
--
--   It is the ball of radius $\varepsilon$ around the nominal distribution, the set of distributions the adversary may choose in the worst-case risk.
--
--   **Formalization Note** "Supported on $\Xi$" is encoded as $\mathbb Q(\Xi^c) = 0$; for $\Xi = E$ this is no condition. Closedness of $\Xi$ is a hypothesis of the statements that need it.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §1, p. 6 (definition of P(Ξ) and B_{ε,p}(P̂N))

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_wasserstein

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **The Wasserstein ambiguity set `B_{ε,p}(P)`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §1, p. 6: "we let Ξ ⊆ R^m be a closed set that is known to contain the support of P. … we
denote by P(Ξ) the family of all probability distributions supported on Ξ, and we define the
ambiguity set B_{ε,p}(P̂N) = {Q ∈ P(Ξ) : W_p(Q, P̂N) ≤ ε} as the ball of radius ε ≥ 0 in P(Ξ)
centered at the nominal distribution P̂N with respect to the type-p Wasserstein distance."

`ambiguityBall ε p P Ξ` is the set of Borel probability measures `Q` on `E` with `Q(E ∖ Ξ) = 0` and
`W_p(Q, P) ≤ ε`.

**Formalization Note.** "Supported on Ξ" is read as `Q(Ξᶜ) = 0`; for `Ξ = ℝ^m` this is no condition.
The centre `P` is any measure (the paper's nominal distribution `P̂_N`); the radius is compared in
`[0, ∞]` through `ENNReal.ofReal ε`. Closedness of `Ξ` is a hypothesis of the statements that need
it, not part of the definition. -/
def ambiguityBall {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (ε p : ℝ)
    (P : Measure E) (Ξ : Set E) : Set (Measure E) :=
  {Q | IsProbabilityMeasure Q ∧ Q Ξᶜ = 0 ∧ wasserstein p Q P ≤ ENNReal.ofReal ε}

end WassersteinDRO.ConvexLossP1


