-- Prove2me | Definitions.Def_NemirovskiProx_Hfun
-- name    : NemirovskiProx_Hfun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:44:41.722699+00:00
-- url     : https://prove2.me/theorems/2e67f659-787b-45a2-9f6d-a960a3cbcdd1
-- title:
--   The function $H_u(z)=\Omega_u(\omega'(z))$, (2.3)
-- statement:
--   For $u\in E$ let $\Omega_u(\xi)=\Omega(\xi)-\langle\xi,u\rangle$, and define, for $z\in Z$,
--   $$H_u(z)=\Omega_u(\omega'(z))=\Omega(\omega'(z))-\langle\omega'(z),u\rangle. \tag{2.3}$$
--
--   $H_u$ plays the role of a Bregman-type distance from $z$ to $u$: Lemma 2.1 and Lemma 3.1 bound its decrease along one prox step.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, §2.2, eq. (2.3), p. 232

import Mathlib
import Definitions.Def_NemirovskiProx_legendre

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The function `H_u(z) = Ω_u(ω′(z))`, (2.3).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), §2.2, (2.3), p. 232: "Ωu(ξ) = Ω(ξ) − ⟨ξ, u⟩ : E → R, Hu(z) = Ωu(ω′(z)) : Z → R."

`Hfun Z ω ω' u z = Ω(ω' z) − ⟨ω' z, u⟩`, with `Ω = legendre Z ω`. -/
noncomputable def Hfun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Z : Set E) (ω : E → ℝ) (ω' : E → E) (u z : E) : ℝ :=
  legendre Z ω (ω' z) - ⟪ω' z, u⟫_ℝ

end NemirovskiProx


