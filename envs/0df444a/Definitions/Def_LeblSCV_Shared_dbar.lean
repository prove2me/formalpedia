-- Prove2me | Definitions.Def_LeblSCV_Shared_dbar
-- name    : LeblSCV_Shared_dbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T08:21:55.052268+00:00
-- url     : https://prove2.me/theorems/6ad35a9d-d853-4c9a-8b18-e4a508759a76
-- title:
--   Wirtinger operator $\partial/\partial\bar z$ in one variable
-- statement:
--   For a function $f : \mathbb{C} \to \mathbb{C}$ and a point $z = x + iy$, the **Wirtinger derivative** with respect to $\bar z$ is
--   $$\frac{\partial f}{\partial \bar z}(z) = \frac{1}{2}\left( \frac{\partial f}{\partial x}(z) + i\,\frac{\partial f}{\partial y}(z) \right),$$
--   where $\frac{\partial f}{\partial x}(z)$ is the derivative at $t = 0$ of the real-variable function $t \mapsto f(z + t)$ and $\frac{\partial f}{\partial y}(z)$ that of $t \mapsto f(z + it)$.
--
--   A $C^1$ function is holomorphic exactly where $\partial f/\partial \bar z = 0$; the operator is the one-variable $\bar\partial$ appearing in the Cauchy–Pompeiu formula (Theorem 4.1.1, p. 130) and in Lemma 4.4.6 (p. 141), which solves $\partial\psi/\partial\bar z = g$ on a disc. It serves chunk VI (Theorem 4.1.1, p. 130, and Lemma 4.4.6, p. 141) and chunk VII (Lemma 4.4.6, p. 141). For example $\partial \bar z/\partial \bar z = 1$ and $\partial z/\partial \bar z = 0$.
--
--   **Formalization Note.** The partial derivatives are Mathlib's `deriv` of the real-variable restrictions. `deriv` returns $0$ where the derivative does not exist; the operator is only applied to functions that are $C^1$ or smooth at the point in question.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 15 (Wirtinger operators), used on pp. 130 and 141

import Mathlib

open Complex

namespace LeblSCV.Shared

/-- The one-variable Wirtinger operator `∂/∂z̄ = (1/2)(∂/∂x + i ∂/∂y)` (Lebl, p. 15, used in
Theorem 4.1.1 and Lemma 4.4.6), where `z = x + i y`: `∂f/∂x (z)` is the derivative at `t = 0` of the
real-variable function `t ↦ f(z + t)` and `∂f/∂y (z)` that of `t ↦ f(z + i t)`. -/
noncomputable def dbar (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z =>
    (1 / 2 : ℂ) *
      (deriv (fun t : ℝ => f (z + (t : ℂ))) 0 +
        I * deriv (fun t : ℝ => f (z + (t : ℂ) * I)) 0)

end LeblSCV.Shared


