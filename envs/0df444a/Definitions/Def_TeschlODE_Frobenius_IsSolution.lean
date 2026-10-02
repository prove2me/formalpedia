-- Prove2me | Definitions.Def_TeschlODE_Frobenius_IsSolution
-- name    : TeschlODE_Frobenius_IsSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:11:32.191911+00:00
-- url     : https://prove2.me/theorems/15da8db7-1ab4-47f9-9783-b260f8ec66c1
-- title:
--   Solution of the second-order equation u'' + p(z)u' + q(z)u = 0, Eq. (4.20)
-- statement:
--   Let $p, q : \mathbb{C} \to \mathbb{C}$ and let $D \subseteq \mathbb{C}$ be an open set. A function $u$ is a **solution** of the second-order linear equation
--   $$u''(z) + p(z)\,u'(z) + q(z)\,u(z) = 0 \qquad (4.20)$$
--   on $D$ if at every $z \in D$ the function $u$ and its complex derivative $u'$ are complex differentiable and the equation holds at $z$.
--
--   **Formalization Note.** Derivatives are complex derivatives (`deriv`, `DifferentiableAt ℂ`). Every use in this mission takes $D$ open (a slit disc), so $u$ is holomorphic on $D$ and `deriv u` is its true derivative near each point of $D$. Only the values of $p, q, u$ on $D$ enter.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 116, §4.2, Eq. (4.20)

import Mathlib

namespace TeschlODE.Frobenius

/-- Teschl (4.20), p. 116: `u` solves the second-order linear equation
`u'' + p(z) u' + q(z) u = 0` on the (open) set `D ⊆ ℂ`: at every `z ∈ D`, `u` and its complex
derivative `deriv u` are complex differentiable at `z`, and the equation holds at `z`.
Every use in this mission takes `D` open (a slit disc), so `deriv u` is the true derivative of `u`
on a neighbourhood of each point of `D`. -/
def IsSolution (p q : ℂ → ℂ) (D : Set ℂ) (u : ℂ → ℂ) : Prop :=
  ∀ z ∈ D, DifferentiableAt ℂ u z ∧ DifferentiableAt ℂ (deriv u) z ∧
    deriv (deriv u) z + p z * deriv u z + q z * u z = 0

end TeschlODE.Frobenius


