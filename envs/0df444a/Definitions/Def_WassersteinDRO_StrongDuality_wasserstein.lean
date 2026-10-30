-- Prove2me | Definitions.Def_WassersteinDRO_StrongDuality_wasserstein
-- name    : WassersteinDRO_StrongDuality_wasserstein
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:56:29.97098+00:00
-- url     : https://prove2.me/theorems/07b498ad-dc80-450b-a990-8e968e1b5262
-- title:
--   Type-$p$ Wasserstein distance $W_p(\mathbb Q, \mathbb Q')$
-- statement:
--   Let $(E, \|\cdot\|)$ be a normed space with its Borel $\sigma$-algebra, let $p \in [1, \infty)$, and let $\mathbb Q, \mathbb Q'$ be probability measures on $E$. The **type-$p$ Wasserstein distance** is
--   $$W_p(\mathbb Q, \mathbb Q') = \Big( \inf_{\pi \in \Pi(\mathbb Q, \mathbb Q')} \int_{E \times E} \|\xi - \xi'\|^p \, \pi(\mathrm d\xi, \mathrm d\xi') \Big)^{1/p} \in [0, \infty].$$
--
--   It is the minimal cost of transporting $\mathbb Q$ onto $\mathbb Q'$ when moving a unit of mass from $\xi$ to $\xi'$ costs $\|\xi - \xi'\|^p$. The norm is arbitrary, as in the paper.
--
--   **Formalization Note** The distance takes values in $[0, \infty]$: the paper notes that it is finite whenever both distributions have finite $p$-th moments, and it can be $+\infty$ otherwise. The cost is integrated as a nonnegative extended real, so no integrability condition is needed.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Definition 1, eq. (5), p. 3

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_couplings

open MeasureTheory

namespace WassersteinDRO.StrongDuality

/-- **The type-`p` Wasserstein distance `W_p(Q, Q')`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Definition 1, eq. (5), p. 3: "For any p ∈ [1, ∞), the type-p Wasserstein distance between two
probability distributions Q and Q′ on R^m is defined as
W_p(Q, Q′) = ( inf_{π∈Π(Q,Q′)} ∫_{R^m×R^m} ‖ξ − ξ′‖^p π(dξ, dξ′) )^{1/p}, where ‖·‖ is a norm on
R^m".

`wasserstein p Q Q'` is `(⨅_{π ∈ Π(Q, Q')} ∫⁻ ‖ξ − ξ'‖^p dπ)^{1/p}`, with values in `[0, ∞]`.

**Formalization Note.** The value `+∞` is a genuine value: the paper notes (p. 3) that `W_p` is
finite whenever both distributions have finite `p`-th moments, and it may be infinite otherwise.
The norm is the space's own norm, an arbitrary norm on `ℝ^m` as in the paper. The cost is
integrated as a nonnegative extended real (`lintegral`), so no integrability condition enters.
The statements use `1 ≤ p`; for probability measures the coupling set is nonempty, so the
infimum is not the empty-set value `⊤`. -/
noncomputable def wasserstein {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (p : ℝ)
    (Q Q' : Measure E) : ENNReal :=
  (⨅ π ∈ couplings Q Q', ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π) ^ (1 / p)

end WassersteinDRO.StrongDuality


