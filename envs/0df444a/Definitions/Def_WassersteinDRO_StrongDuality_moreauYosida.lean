-- Prove2me | Definitions.Def_WassersteinDRO_StrongDuality_moreauYosida
-- name    : WassersteinDRO_StrongDuality_moreauYosida
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:58:14.874061+00:00
-- url     : https://prove2.me/theorems/c4422c1e-12c5-4e02-a968-4f8ca5aaadf5
-- title:
--   Moreau–Yosida regularization $\ell_\gamma(\xi) = \sup_{z \in \Xi} \ell(z) - \gamma \|z - \xi\|^p$
-- statement:
--   Let $(E, \|\cdot\|)$ be a normed space, $\Xi \subseteq E$, $\ell : E \to [-\infty, +\infty]$, $\gamma \in \mathbb R$ and $p \in \mathbb R$. The **Moreau–Yosida regularization** of $\ell$ over $\Xi$ is the function
--   $$\ell_\gamma(\xi) = \sup_{z \in \Xi} \; \ell(z) - \gamma \|z - \xi\|^p, \qquad \xi \in E,$$
--   with values in $[-\infty, +\infty]$.
--
--   It is the integrand of the dual problem (10): $\gamma \ge 0$ is the price per unit of transportation cost, and $\ell_\gamma(\xi)$ is the largest loss an adversary can reach from $\xi$ after paying for moving it. For $\xi \in \Xi$ and $p > 0$ one has $\ell_\gamma(\xi) \ge \ell(\xi)$, and $\ell_\gamma$ decreases in $\gamma \ge 0$.
--
--   **Formalization Note** The supremum is over $z \in \Xi$ and is taken in $[-\infty, +\infty]$ ($-\infty$ for empty $\Xi$). Only the real number $\gamma\|z - \xi\|^p$ is subtracted from $\ell(z)$, so no $\infty - \infty$ arises. The power is the real power, with the same exponent $p$ as in the Wasserstein distance.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Theorem 7, p. 10 (ℓγ(ξ) = sup_{z∈Ξ} ℓ(z) − γ‖z − ξ‖^p)

import Mathlib

namespace WassersteinDRO.StrongDuality

/-- **The Moreau–Yosida regularization `ℓ_γ` of a loss over `Ξ`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Theorem 7, p. 10: "where ℓγ(ξ) = sup_{z∈Ξ} ℓ(z) − γ‖z − ξ‖^p is a Moreau-Yosida
regularization [77] of ℓ(ξ)."

`moreauYosida ℓ Ξ γ p ξ` is `sup_{z ∈ Ξ} (ℓ(z) − γ ‖z − ξ‖^p)`, a value in `[−∞, +∞]`.

**Formalization Note.** The supremum is taken in the complete lattice `EReal` over `z ∈ Ξ` (not
over the whole space); it is `−∞` for empty `Ξ`. Only a real number `γ ‖z − ξ‖^p` is subtracted
from the extended real `ℓ(z)`, so no `∞ − ∞` arises (`⊤ − r = ⊤`, `⊥ − r = ⊥`). The power is the
real power `Real.rpow` with the same exponent `p` as in the Wasserstein distance, and the norm is
the space's own norm. As a supremum of continuous functions of `ξ` it is lower semicontinuous,
hence Borel measurable. -/
noncomputable def moreauYosida {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E)
    (γ p : ℝ) (ξ : E) : EReal :=
  ⨆ z ∈ Ξ, ℓ z - ((γ * ‖z - ξ‖ ^ p : ℝ) : EReal)

end WassersteinDRO.StrongDuality


