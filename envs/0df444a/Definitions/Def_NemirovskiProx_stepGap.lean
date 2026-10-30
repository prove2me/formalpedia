-- Prove2me | Definitions.Def_NemirovskiProx_stepGap
-- name    : NemirovskiProx_stepGap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:45:17.575613+00:00
-- url     : https://prove2.me/theorems/24b60052-852b-4d09-b618-5f5e6f39cc73
-- title:
--   Left-hand side of (2.11) and (3.4)
-- statement:
--   For $z,w,w',\xi\in E$ let
--   $$\mathrm{gap}(z,w,w',\xi)=\langle\xi,w-w'\rangle+\omega(z)+\langle\omega'(z),w'-z\rangle-\omega(w').$$
--
--   In (2.11) it is evaluated at $z=z_{t-1}$, $w=w_t$, $w'=z_t=P_{z_{t-1}}(\gamma_tF(w_t))$, $\xi=\gamma_tF(w_t)$; in the stopping test (3.4) of the basic implementation at $z=z_{t-1}$, $w=w_{t,s-1}$, $w'=w_{t,s}$, $\xi=\gamma F(w_{t,s-1})$. A step is accepted when this quantity is at most $\epsilon_t$, respectively $0$.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, eq. (2.11), p. 234, and eq. (3.4), p. 237

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The left-hand side of (2.11) and (3.4).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), (2.11), p. 234: "⟨wt − Pzt−1(γtF(wt)), γtF(wt)⟩ + ω(zt−1) + ⟨ω′(zt−1),
Pzt−1(γtF(wt)) − zt−1⟩ − ω(Pzt−1(γtF(wt)))"; (3.4), p. 237: "⟨γF(wt,s−1), wt,s−1 − wt,s⟩ +
ω(zt−1) + ⟨ω′(zt−1), wt,s − zt−1⟩ − ω(wt,s)".

`stepGap ω ω' z w w' ξ = ⟨ξ, w − w'⟩ + ω z + ⟨ω' z, w' − z⟩ − ω w'`.
In (2.11): `z = z_{t−1}`, `w = w_t`, `w' = z_t = P_{z_{t−1}}(γ_t F(w_t))`, `ξ = γ_t F(w_t)`.
In (3.4): `z = z_{t−1}`, `w = w_{t,s−1}`, `w' = w_{t,s}`, `ξ = γ F(w_{t,s−1})`. -/
def stepGap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ω : E → ℝ) (ω' : E → E) (z w w' ξ : E) : ℝ :=
  ⟪ξ, w - w'⟫_ℝ + ω z + ⟪ω' z, w' - z⟫_ℝ - ω w'

end NemirovskiProx


