-- Prove2me | Definitions.Def_LeblSCV_Shared_wirtingerBar
-- name    : LeblSCV_Shared_wirtingerBar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T08:29:41.473034+00:00
-- url     : https://prove2.me/theorems/36763326-0d1b-4721-bcab-d000c413059a
-- title:
--   Wirtinger operator $\partial/\partial\bar z_k$ on $\mathbb{C}^n$
-- statement:
--   For a function $f : \mathbb{C}^n \to \mathbb{C}$, an index $k \in \{1, \dots, n\}$ and a point $z$ with $z_k = x_k + i y_k$, the **Wirtinger derivative** with respect to $\bar z_k$ is
--   $$\frac{\partial f}{\partial \bar z_k}(z) = \frac{1}{2}\left( \frac{\partial f}{\partial x_k}(z) + i\,\frac{\partial f}{\partial y_k}(z) \right),$$
--   where $\frac{\partial f}{\partial x_k}(z)$ is the derivative at $t = 0$ of $t \mapsto f(z_1, \dots, z_k + t, \dots, z_n)$ and $\frac{\partial f}{\partial y_k}(z)$ that of $t \mapsto f(z_1, \dots, z_k + it, \dots, z_n)$ ($t$ real).
--
--   For a smooth $\psi$ these are the coefficients of $\bar\partial \psi = \frac{\partial \psi}{\partial \bar z_1} d\bar z_1 + \cdots + \frac{\partial \psi}{\partial \bar z_n} d\bar z_n$. It serves chunk VI (the compactly supported $\bar\partial$-problem, Theorem 4.2.1, p. 132, where $\bar\partial\psi = g$ is the system $\partial\psi/\partial\bar z_k = g_k$) and chunk VII (the coefficients of the operator $\bar\partial$ on differential forms, Definition 4.4.1, p. 138).
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ` (indices $0, \dots, n-1$). The partial derivatives are Mathlib's `deriv` of real-variable restrictions, which is $0$ where the derivative does not exist; the operator is only applied to smooth functions.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 15 (Wirtinger operators), used on pp. 132 and 138

import Mathlib

open Complex

namespace LeblSCV.Shared

/-- The Wirtinger operator `∂/∂z̄_k = (1/2)(∂/∂x_k + i ∂/∂y_k)` on `ℂⁿ` (Lebl, p. 15; used in §4.2 to
write `∂̄ψ = ∂ψ/∂z̄_1 dz̄_1 + ⋯ + ∂ψ/∂z̄_n dz̄_n`), where `z_k = x_k + i y_k`: `∂f/∂x_k (z)` is the
derivative at `t = 0` of the real-variable function `t ↦ f(z_1, …, z_k + t, …, z_n)` and
`∂f/∂y_k (z)` that of `t ↦ f(z_1, …, z_k + i t, …, z_n)`. -/
noncomputable def wirtingerBar {n : ℕ} (k : Fin n) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z =>
    (1 / 2 : ℂ) *
      (deriv (fun t : ℝ => f (Function.update z k (z k + (t : ℂ)))) 0 +
        I * deriv (fun t : ℝ => f (Function.update z k (z k + (t : ℂ) * I))) 0)

end LeblSCV.Shared


