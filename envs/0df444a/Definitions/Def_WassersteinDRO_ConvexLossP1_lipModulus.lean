-- Prove2me | Definitions.Def_WassersteinDRO_ConvexLossP1_lipModulus
-- name    : WassersteinDRO_ConvexLossP1_lipModulus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:50:42.805589+00:00
-- url     : https://prove2.me/theorems/2d618f30-deb0-459c-b048-dd97fcd51245
-- title:
--   Lipschitz modulus $\mathrm{Lip}(\ell)$ of an extended real-valued function
-- statement:
--   Let $(E, \|\cdot\|)$ be a normed space and $\ell : E \to [-\infty, +\infty]$. The **Lipschitz modulus** of $\ell$ is
--   $$\mathrm{Lip}(\ell) = \sup_{\xi \ne \xi'} \frac{|\ell(\xi) - \ell(\xi')|}{\|\xi - \xi'\|} \in [0, \infty].$$
--
--   It is the slope of the steepest line segment joining two points of the graph; $\ell$ is Lipschitz continuous exactly when $\mathrm{Lip}(\ell) < \infty$.
--
--   **Formalization Note** $|\pm\infty| = \infty$. When $\ell(\xi)$ and $\ell(\xi')$ are infinite with the same sign, the paper's quotient is undefined and Lean assigns it the value $\infty$; this changes no value whenever $\ell$ takes at least one finite value (as under the paper's Assumption 1), because then any infinite value already forces $\mathrm{Lip}(\ell) = \infty$. For a one-point space the supremum is over the empty set and equals $0$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §1, p. 4 (unnumbered definition of Lip(ϕ))

import Mathlib

namespace WassersteinDRO.ConvexLossP1

/-- **The Lipschitz modulus `Lip(ℓ)` of an extended real-valued function.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §1, p. 4: "we define the Lipschitz modulus of an extended real-valued function ϕ on R^m with
respect to the norm ‖·‖ as Lip(ϕ) = sup_{ξ≠ξ′} |ϕ(ξ) − ϕ(ξ′)| / ‖ξ − ξ′‖."

`lipModulus ℓ` is `sup_{x ≠ y} |ℓ(x) − ℓ(y)| / ‖x − y‖`, with values in `[0, ∞]`.

**Formalization Note.** `EReal.abs` sends `±∞` to `∞`. When `ℓ(x)` and `ℓ(y)` are infinite of the
same sign the paper's quotient is undefined; Lean's `⊤ − ⊤ = ⊥` and `⊥ − ⊥ = ⊥` give it the value
`∞`. This changes no value whenever `ℓ` takes at least one finite value (as it does under the
paper's Assumption 1, p. 9): then any infinite value of `ℓ` already makes the paper's `Lip(ℓ) = ∞`
through the pair (infinite point, finite point). The denominator is positive because `x ≠ y`. For
`E` a single point the supremum is over the empty set and equals `0`. -/
noncomputable def lipModulus {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) : ENNReal :=
  ⨆ (x : E) (y : E) (_ : x ≠ y), EReal.abs (ℓ x - ℓ y) / ENNReal.ofReal ‖x - y‖

end WassersteinDRO.ConvexLossP1


