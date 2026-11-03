-- Prove2me | Definitions.Def_DCAExtrap_objF
-- name    : DCAExtrap_objF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:27.949206+00:00
-- url     : https://prove2.me/theorems/74b20249-c8bd-418d-a28a-0ee5388cfdb5
-- title:
--   Objective $F = f + g - h$ of problem (1)
-- statement:
--   For $f,h:E\to\mathbb R$ and $g:E\to(-\infty,+\infty]$, the objective of problem (1) is
--
--   $$
--   F(x) := f(x) + g(x) - h(x).
--   $$
--
--   $F(x)=+\infty$ exactly when $g(x)=+\infty$. Problem (1) is $\min_{x\in E}F(x)$.
--
--   **Formalization Note** $F$ is `EReal`-valued; since $f$ and $h$ are finite no $\infty-\infty$ occurs.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, (1), p.1

import Mathlib

namespace DCAExtrap

/-- **The objective of problem (1)** (Phan–Le Thi, arXiv:2106.04743v1, (1), p.1):
`F(x) := f(x) + g(x) − h(x)`.

**Formalization Note.** `f, h : E → ℝ` are real-valued and `g : E → EReal` may take the value
`+∞`, so `F` is `EReal`-valued; since `f` and `h` are finite no `∞ − ∞` occurs, and `F x = ⊤`
exactly when `g x = ⊤`. -/
noncomputable def objF {E : Type*} (f : E → ℝ) (g : E → EReal) (h : E → ℝ) (x : E) : EReal :=
  ((f x : ℝ) : EReal) + g x - ((h x : ℝ) : EReal)

end DCAExtrap


