-- Prove2me | Definitions.Def_WassersteinDRO_Duality_moreauYosida
-- name    : WassersteinDRO_Duality_moreauYosida
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:17:24.292346+00:00
-- url     : https://prove2.me/theorems/9e261165-046c-4584-a9cc-1ded9e0888ad
-- title:
--   Moreau-Yosida regularization of a loss function
-- statement:
--   For a bounded continuous loss function $\ell$ on $E$, a support set $\Xi \subseteq E$,
--   an exponent $p$ and a regularization level $\gamma \ge 0$, the Moreau-Yosida
--   regularization of $\ell$ at $\xi$ is
--   $$\ell_\gamma(\xi) = \sup_{z \in \Xi} \ell(z) - \gamma\|z-\xi\|^p.$$
--   Restricting $\ell$ to bounded continuous functions (rather than the paper's general
--   upper-semicontinuous, integrable loss class $\mathcal{L}$) keeps this supremum a finite
--   real number for every nonempty $\Xi$: it is bounded above by $\sup \ell$ and bounded
--   below by evaluating the inner expression at any fixed $z_0 \in \Xi$.
-- source:
--   Kuhn et al. 2019, Theorem 7, p. 10

import Mathlib

namespace WassersteinDRO.Duality

/-- The Moreau-Yosida regularization of a bounded continuous loss function `ℓ` at level `γ`,
with respect to the type-`p` transportation cost on the support set `Ξ`, Kuhn et al. 2019,
Theorem 7, p. 10: `ℓγ(ξ) = sup_{z∈Ξ} ℓ(z) - γ‖z-ξ‖^p`. Restricting `ℓ` to bounded continuous
functions (`BoundedContinuousFunction E ℝ`), rather than the paper's general upper-semicontinuous, `PN`-integrable
`ℓ ∈ L` (Assumption 1, p. 9), keeps the pointwise supremum a finite real number whenever `Ξ`
is nonempty: with `ℓ` bounded by `M`, `ℓγ(ξ) ≤ M`, and picking any `z₀ ∈ Ξ` gives
`ℓγ(ξ) ≥ ℓ(z₀) - γ‖z₀-ξ‖^p > -∞`, so the defining set is nonempty and bounded above and
Mathlib's real `sSup` returns the genuine supremum, not its junk value on an unbounded or
empty set. This is a disclosed narrowing of the loss class for the goal theorem only; see
`STATUS.md` / `MODERATION_NOTES.md`. -/
noncomputable def moreauYosida {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : BoundedContinuousFunction E ℝ) (p γ : ℝ) (ξ : E) : ℝ :=
  sSup ((fun z => ℓ z - γ * ‖z - ξ‖ ^ p) '' Ξ)

end WassersteinDRO.Duality


