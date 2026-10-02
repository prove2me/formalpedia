-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_SLOp
-- name    : TeschlODE_SturmLiouville_SLOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:20:57.036598+00:00
-- url     : https://prove2.me/theorems/7602d6a0-8dd4-4431-86f3-96a271831957
-- title:
--   The Sturm–Liouville differential expression L (5.53)
-- statement:
--   Given coefficients $p, q, r$ on $[a,b]$ and a function $f : [a,b] \to \mathbb{C}$, the **Sturm–Liouville expression** is
--   $$(L f)(x) = \frac{1}{r(x)}\Bigl( -\bigl(p(x) f'(x)\bigr)' + q(x) f(x) \Bigr), \qquad x \in [a,b]. \qquad (5.53)$$
--   The equation $L f = z f$ is (5.43) divided by $r > 0$.
--
--   **Formalization Note.** Both derivatives are `derivWithin … (Set.Icc a b)`, i.e. one-sided at $a$ and $b$. The expression is only used for $f \in C^2([a,b],\mathbb{C})$ and $x \in [a,b]$; outside that range its value is irrelevant.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 155, §5.4, Eq. (5.53)

import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.4, p. 155, (5.53): the Sturm–Liouville differential expression
`L f = r⁻¹ (−(p f′)′ + q f)` applied to `f : [a, b] → ℂ`, evaluated at `x`. Derivatives are taken
within `[a, b]` (one-sided at the endpoints). Only the values at `x ∈ [a, b]` are meaningful. -/
noncomputable def SLOp (p q r : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((r x : ℂ))⁻¹ *
    (-derivWithin (fun y => (p y : ℂ) * derivWithin f (Set.Icc a b) y) (Set.Icc a b) x +
      (q x : ℂ) * f x)

end TeschlODE.SturmLiouville


