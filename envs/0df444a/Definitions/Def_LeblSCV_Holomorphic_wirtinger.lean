-- Prove2me | Definitions.Def_LeblSCV_Holomorphic_wirtinger
-- name    : LeblSCV_Holomorphic_wirtinger
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:00:53.330255+00:00
-- url     : https://prove2.me/theorems/645a71c9-80d0-436a-a116-08b54287adc6
-- title:
--   Wirtinger operator $\partial/\partial z_k$
-- statement:
--   Write $z_k = x_k + i y_k$. For a function $f$ on an open subset of $\mathbb{C}^n$, the **Wirtinger derivative** in $z_k$ is
--   $$\frac{\partial f}{\partial z_k} = \frac{1}{2}\left( \frac{\partial f}{\partial x_k} - i \frac{\partial f}{\partial y_k} \right),$$
--   where $\frac{\partial f}{\partial x_k}(z)$ and $\frac{\partial f}{\partial y_k}(z)$ are the ordinary real partial derivatives, i.e. the derivatives at $t = 0$ of the real-variable functions $t \mapsto f(z_1, \dots, z_k + t, \dots, z_n)$ and $t \mapsto f(z_1, \dots, z_k + i t, \dots, z_n)$.
--
--   For a holomorphic $f$ this agrees with the complex partial derivative in Definition 1.1.2, and it is the operator $\partial/\partial z_k$ used in Proposition 1.1.3, in the multi-index derivatives $\partial^{|\alpha|}/\partial z^\alpha$, and in the holomorphic Jacobian $Df(p) = [\partial f_k/\partial z_\ell(p)]$.
--
--   **Formalization Note.** The real partial derivatives are Mathlib's `deriv` of the real-variable functions above, which is $0$ where the one-sided derivative does not exist; the theorems of this mission apply the operator only to holomorphic functions, which are $C^\infty$ by Proposition 1.1.3.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 15 (definition of the Wirtinger operators)

import Mathlib

open Complex

namespace LeblSCV.Holomorphic

/-- The Wirtinger operator `∂/∂z_k = (1/2)(∂/∂x_k - i ∂/∂y_k)` (Lebl, p. 15), where `z_k = x_k + i y_k`
and `∂/∂x_k`, `∂/∂y_k` are the real partial derivatives: `∂f/∂x_k (z)` is the derivative at `t = 0`
of the real-variable function `t ↦ f(z_1, …, z_k + t, …, z_n)`, and `∂f/∂y_k (z)` that of
`t ↦ f(z_1, …, z_k + i t, …, z_n)`. -/
noncomputable def wirtinger {n : ℕ} (k : Fin n) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z =>
    (1 / 2 : ℂ) *
      (deriv (fun t : ℝ => f (Function.update z k (z k + (t : ℂ)))) 0 -
        I * deriv (fun t : ℝ => f (Function.update z k (z k + (t : ℂ) * I))) 0)

end LeblSCV.Holomorphic


