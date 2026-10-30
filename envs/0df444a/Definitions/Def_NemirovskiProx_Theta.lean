-- Prove2me | Definitions.Def_NemirovskiProx_Theta
-- name    : NemirovskiProx_Theta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:44:56.974042+00:00
-- url     : https://prove2.me/theorems/a79c3dd9-bea1-4f2e-b643-af582a302717
-- title:
--   The quantity $\Theta(z_0)$, (2.13)
-- statement:
--   For $z_0\in Z$,
--   $$\Theta(z_0)=\max_{z\in Z}\,\big[\omega(z)-\omega(z_0)-\langle\omega'(z_0),z-z_0\rangle\big].$$
--
--   It is the largest Bregman distance from $z_0$ to a point of $Z$, and it is the numerator of the error bounds (2.13), (2.14), (3.9) and (3.10).
--
--   **Formalization Note** The maximum is a supremum of the image of $Z$; wherever it is used $Z$ is nonempty and compact and $\omega$ is continuous on $Z$, so it is attained.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Proposition 2.2, eq. (2.13), p. 234

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The quantity `Θ(z₀)`, (2.13).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Proposition 2.2, (2.13), p. 234: "Θ(z0) = max_{z∈Z} [ω(z) − ω(z0) − ⟨ω′(z0), z − z0⟩]."

`Theta Z ω ω' z0 = sup_{v ∈ Z} (ω v − ω z0 − ⟨ω' z0, v − z0⟩)`.

**Formalization Note.** The paper's `max` is `sSup` of the image of `Z`; wherever it is used
`Z` is nonempty and compact and `ω` is continuous on `Z`, so the supremum is a max. -/
noncomputable def Theta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Z : Set E) (ω : E → ℝ) (ω' : E → E) (z0 : E) : ℝ :=
  sSup ((fun v => ω v - ω z0 - ⟪ω' z0, v - z0⟫_ℝ) '' Z)

end NemirovskiProx


