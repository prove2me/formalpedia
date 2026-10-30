-- Prove2me | Definitions.Def_NemirovskiProx_legendre
-- name    : NemirovskiProx_legendre
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:44:13.887992+00:00
-- url     : https://prove2.me/theorems/63ffa08b-b939-4c32-b463-5a60058edd4d
-- title:
--   Legendre transformation $\Omega$ of $\omega|_Z$
-- statement:
--   For $Z\subset E$ and $\omega:Z\to\mathbb R$, the **Legendre transformation** of $\omega|_Z$ is
--   $$\Omega(\xi)=\max_{z\in Z}\,\big[\langle\xi,z\rangle-\omega(z)\big],\qquad \xi\in E.$$
--
--   It enters the potential $H_u$ of (2.3), which drives the convergence analysis of the prox-method.
--
--   **Formalization Note** The maximum is a supremum of the image of $Z$; wherever it is used $Z$ is nonempty and compact and $\omega$ is continuous on $Z$, so the supremum is attained.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, §2.2, p. 232 (definition of Ω before (2.3))

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The Legendre transformation `Ω` of `ω|_Z`.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), §2.2, p. 232: "Let also Ω(ξ) = max_{z∈Z}[⟨ξ, z⟩ − ω(z)] be the Legendre transformation
of ω|_Z".

`legendre Z ω ξ = sup_{v ∈ Z} (⟨ξ, v⟩ − ω v)`.

**Formalization Note.** The paper's `max` is `sSup` of the image of `Z`. Wherever it is used
in this mission `Z` is nonempty and compact and `ω` is continuous on `Z` (it has a gradient
within `Z` at each point), so the image is nonempty, bounded and its supremum is attained. On
an empty `Z` the value would be the junk `0`; that input never occurs. -/
noncomputable def legendre {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Z : Set E) (ω : E → ℝ) (ξ : E) : ℝ :=
  sSup ((fun v => ⟪ξ, v⟫_ℝ - ω v) '' Z)

end NemirovskiProx


