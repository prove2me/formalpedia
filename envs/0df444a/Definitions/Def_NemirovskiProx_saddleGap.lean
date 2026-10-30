-- Prove2me | Definitions.Def_NemirovskiProx_saddleGap
-- name    : NemirovskiProx_saddleGap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:47:50.503592+00:00
-- url     : https://prove2.me/theorems/c528e0b8-52da-4da9-8464-3308322f33b3
-- title:
--   Saddle point inaccuracy $\epsilon_f(x,y)$, (2.14)
-- statement:
--   For $X\subset E_x$, $Y\subset E_y$, $f:X\times Y\to\mathbb R$ and $(x,y)\in X\times Y$,
--   $$\epsilon_f(x,y)=\Big[\max_{y'\in Y}f(x,y')-\min_{x'\in X}\max_{y'\in Y}f(x',y')\Big]+\Big[\max_{y'\in Y}\min_{x'\in X}f(x',y')-\min_{x'\in X}f(x',y)\Big].$$
--
--   It is the sum of the primal and the dual optimality gaps of $(x,y)$ for the saddle point problem of $f$, the quantity bounded in (2.14) and (3.10).
--
--   **Formalization Note** Every max/min is a supremum/infimum of an image of $X$ or $Y$, nested in the paper's order; wherever it is used $X$, $Y$ are nonempty and compact and $f$ is continuous on $X\times Y$, so all are attained.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Proposition 2.2, eq. (2.14), p. 234

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The saddle point inaccuracy `ϵ_f(x, y)`, (2.14).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Proposition 2.2, (2.14), p. 234: "ϵf(z^N) ≡ [max_{y∈Y} f(x^N, y) − min_{x∈X} max_{y∈Y}
f(x, y)] + [max_{y∈Y} min_{x∈X} f(x, y) − min_{x∈X} f(x, y^N)]".

`saddleGap X Y f x y = (sup_{y′∈Y} f(x, y′) − inf_{x′∈X} sup_{y′∈Y} f(x′, y′)) +
(sup_{y′∈Y} inf_{x′∈X} f(x′, y′) − inf_{x′∈X} f(x′, y))`.

**Formalization Note.** Each `max`/`min` is `sSup`/`sInf` of an image of `X` or `Y`, nested in
the paper's order (`min_x max_y` is `sInf` over `X` of `sSup` over `Y`). Wherever it is used
`X`, `Y` are nonempty and compact and `f` is continuous on `X × Y`, so every image is nonempty
and bounded and every supremum and infimum is attained. -/
noncomputable def saddleGap {Ex Ey : Type*} (X : Set Ex) (Y : Set Ey) (f : Ex × Ey → ℝ)
    (x : Ex) (y : Ey) : ℝ :=
  (sSup ((fun y' => f (x, y')) '' Y) -
      sInf ((fun x' => sSup ((fun y' => f (x', y')) '' Y)) '' X)) +
    (sSup ((fun y' => sInf ((fun x' => f (x', y')) '' X)) '' Y) -
      sInf ((fun x' => f (x', y)) '' X))

end NemirovskiProx


