-- Prove2me | Definitions.Def_SAGA_StronglyConvex_lyapunov
-- name    : SAGA_StronglyConvex_lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:54:06.502928+00:00
-- url     : https://prove2.me/theorems/3c9c0ae9-de09-405e-b00d-a354ae7e4210
-- title:
--   The Lyapunov function $T(x,\{\phi_i\})$ of Theorem 1
-- statement:
--   Let $f_1,\dots,f_n:E\to\mathbb R$ with gradients $f_1',\dots,f_n'$, let $f=\frac1n\sum_i f_i$, let $c\in\mathbb R$ and $x^*\in E$. For a SAGA state $(x,\phi)$ the **Lyapunov function** is
--
--   $$
--   T(x,\{\phi_i\}_{i=1}^n)=\frac1n\sum_{i=1}^n f_i(\phi_i)-f(x^*)-\frac1n\sum_{i=1}^n\big\langle f_i'(x^*),\phi_i-x^*\big\rangle+c\,\|x-x^*\|^2 .
--   $$
--
--   This is the function $T$ of Theorem 1 of Defazio, Bach and Lacoste-Julien; in the theorems $x^*$ is the minimizer of the composite objective and $c=1/(2\gamma(1-\gamma\mu)n)$. When the $f_i$ are convex, the first three terms form an average of Bregman divergences and are nonnegative.
--
--   **Formalization Note** $f(x^*)$ is written out as $\frac1n\sum_i f_i(x^*)$; $c$, $x^*$, the $f_i$ and the $f_i'$ are explicit arguments.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 7, Theorem 1 (definition of T)

import Mathlib

open scoped InnerProductSpace

namespace SAGA.StronglyConvex

/-- The Lyapunov function of Theorem 1 (p. 7) at the state `s = (x, φ)`:
`T(x, φ) = (1/n) Σ_i f_i(φ_i) - f(x*) - (1/n) Σ_i ⟨f'_i(x*), φ_i - x*⟩ + c ‖x - x*‖²`,
where `f = (1/n) Σ_i f_i`. -/
noncomputable def lyapunov {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (f : Fin n → E → ℝ) (f' : Fin n → E → E) (c : ℝ) (xs : E) (s : E × (Fin n → E)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f i (s.2 i) - (1 / (n : ℝ)) * ∑ i, f i xs
    - (1 / (n : ℝ)) * ∑ i, ⟪f' i xs, s.2 i - xs⟫_ℝ + c * ‖s.1 - xs‖ ^ 2

end SAGA.StronglyConvex


