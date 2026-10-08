-- Prove2me | Definitions.Def_WassersteinDRO_Duality_moreauYosida_v2
-- name    : WassersteinDRO_Duality_moreauYosida_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:19:19.893784+00:00
-- url     : https://prove2.me/theorems/e373f5c4-70fb-4747-bfb0-38674dfb7913
-- title:
--   Moreau–Yosida regularization $\ell_\gamma$ (extended-real)
-- statement:
--   The Moreau–Yosida regularization of a loss $\ell : E \to \mathbb{R}$ at level $\gamma$ with respect to the type-$p$ transportation cost on the support set $\Xi$ (Theorem 7): $$\ell_\gamma(\xi) = \sup_{z \in \Xi}\, \ell(z) - \gamma\|z-\xi\|^p \in [-\infty,\infty].$$ It is valued in the extended reals because the supremum is genuinely $+\infty$ when $\ell$ grows faster than $\|\cdot\|^p$ (e.g. $\ell(z) = z^2$, $p = 1$), and $-\infty$ when $\Xi = \emptyset$. It replaces the `moreauYosida` that was restricted to bounded continuous losses so that a real-valued supremum would be meaningful.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), Theorem 7, p. 10

import Mathlib

namespace WassersteinDRO.Duality

/-- The Moreau-Yosida regularization of a loss function `ℓ` at level `γ ≥ 0`, with respect to
the type-`p` transportation cost on the support set `Ξ`, Kuhn et al. 2019, Theorem 7, p. 10:
`ℓγ(ξ) = sup_{z ∈ Ξ} ℓ(z) - γ‖z-ξ‖^p`. Valued in `EReal`, because for a loss that grows
faster than `‖·‖^p` the supremum is genuinely `+∞` (e.g. `ℓ(z) = z²`, `p = 1`), and the
paper's right-hand side of (10) then takes the value `+∞`; a real-valued `sSup` would return
the junk value `0` instead. The loss is an arbitrary real-valued function `ℓ : E → ℝ` (the
theorem's standing Assumption 1 — upper semicontinuity and `PN`-integrability — is a
hypothesis of the theorem, not of this definition). This replaces the retired `moreauYosida`,
which was restricted to bounded continuous `ℓ` so that a real `sSup` would be meaningful. -/
noncomputable def moreauYosida {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (ℓ : E → ℝ) (p γ : ℝ) (ξ : E) : EReal :=
  ⨆ (z : E) (_ : z ∈ Ξ), ((ℓ z - γ * ‖z - ξ‖ ^ p : ℝ) : EReal)

end WassersteinDRO.Duality


