-- Prove2me | Definitions.Def_BewleyGE_bellmanObjective
-- name    : BewleyGE_bellmanObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:18.387633+00:00
-- url     : https://prove2.me/theorems/fd1bca7e-a6f8-4763-8d5c-b822c2c9ae9b
-- title:
--   Bellman objective $U(x^*(a-b,p))+\beta\sum_y e(y)f((1+r)b+p\cdot y)$
-- statement:
--   For a demand function $x$, a continuation value $f$, wealth $a$ and savings $b$, the **Bellman objective** is
--   $$
--   U\big(x(a-b)\big)+\beta\sum_{y\in\mathcal Y}e(y)\,f\big((1+r)b+p\cdot y\big).
--   $$
--   Maximizing it over $b\in C(a,p)$ is the right side of the Bellman operator $T$ and of the savings rule (1).
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2.1, p.7 (operator T); (1), p.8

import Mathlib
import Definitions.Def_BewleyGE_Economy

namespace BewleyGE

/-- **Bellman objective** `U(x*(a − b, p)) + β ∑_{y ∈ 𝒴} e(y) f((1 + r) b + p · y)`.
Light, arXiv:1906.06810v2, §2.1, p.7 (the operator `T`) and equation (1), p.8.

Given a demand function `x`, a continuation value `f`, wealth `a` and savings `b`, this is the
value of saving `b` today.

**Formalization Note.** With `x` a demand function (`IsDemand`), `U(x(a − b))` equals the
page's `max_{x ∈ X(a − b, p)} U(x)`. -/
noncomputable def bellmanObjective {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ)
    (x : ℝ → Fin n → ℝ) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  E.U (x (a - b)) + E.β * ∑ y ∈ E.Y, E.e y * f ((1 + r) * b + ∑ i, p i * y i)

end BewleyGE


