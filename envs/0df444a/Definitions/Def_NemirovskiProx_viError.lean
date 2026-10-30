-- Prove2me | Definitions.Def_NemirovskiProx_viError
-- name    : NemirovskiProx_viError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:45:37.437396+00:00
-- url     : https://prove2.me/theorems/7c36269c-1be6-4eaa-81df-11f973fd9753
-- title:
--   Inaccuracy $\epsilon(\bar z)$ of a candidate v.i. solution
-- statement:
--   For $Z\subset E$, $F:Z\to E$ and $\bar z\in Z$,
--   $$\epsilon(\bar z)=\max_{u\in Z}\,\langle F(u),\bar z-u\rangle.$$
--
--   For monotone $F$ this is the standard (weak) measure of how far $\bar z$ is from solving the variational inequality associated with $Z$ and $F$; it is the quantity bounded in (2.13) and (3.9).
--
--   **Formalization Note** The maximum is a supremum of the image of $Z$; wherever it is used $Z$ is nonempty and compact and $F$ is Lipschitz on $Z$, so it is attained.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Proposition 2.2, eq. (2.13), p. 234

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The inaccuracy `ϵ(z̄)` of a candidate solution of the variational inequality, (2.13).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Proposition 2.2, (2.13), p. 234: "ϵ(z^N) ≡ max_{u∈Z} ⟨F(u), z^N − u⟩".

`viError Z F zbar = sup_{u ∈ Z} ⟨F u, zbar − u⟩`.

**Formalization Note.** The paper's `max` is `sSup` of the image of `Z`. Wherever it is used
`Z` is nonempty and compact and `F` is Lipschitz on `Z` in the norm `N` (hence continuous on
`Z`, all norms on the finite-dimensional `E` being equivalent), so the supremum is a max. -/
noncomputable def viError {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Z : Set E) (F : E → E) (zbar : E) : ℝ :=
  sSup ((fun u => ⟪F u, zbar - u⟫_ℝ) '' Z)

end NemirovskiProx


