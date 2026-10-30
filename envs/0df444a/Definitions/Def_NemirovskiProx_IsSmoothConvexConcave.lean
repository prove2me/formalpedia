-- Prove2me | Definitions.Def_NemirovskiProx_IsSmoothConvexConcave
-- name    : NemirovskiProx_IsSmoothConvexConcave
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:47:34.826776+00:00
-- url     : https://prove2.me/theorems/cf3b9bbf-5e6c-4f95-9476-3ddbdd248b8b
-- title:
--   Continuously differentiable convex-concave $f$ on $X\times Y$
-- statement:
--   Let $X\subset E_x$, $Y\subset E_y$, $f:X\times Y\to\mathbb R$, and $f'_x$, $f'_y$ maps on $X\times Y$. The predicate says:
--
--   1. for $x\in X$, $y\in Y$, $f'_x(x,y)$ is the gradient of $f(\cdot,y)$ at $x$ relative to $X$, and $f'_y(x,y)$ is the gradient of $f(x,\cdot)$ at $y$ relative to $Y$;
--   2. $f'_x$ and $f'_y$ are continuous on $X\times Y$;
--   3. $f(\cdot,y)$ is convex on $X$ for every $y\in Y$, and $f(x,\cdot)$ is concave on $Y$ for every $x\in X$.
--
--   This is the paper's "continuously differentiable function $f(x,y):X\times Y\to\mathbb R$ which is convex in $x\in X$ and concave in $y\in Y$", together with its partial gradients.
--
--   **Formalization Note** Differentiability is required only through the partial gradients, relative to $X$ and $Y$; no open set or interior point is assumed. Continuity of $f$ on $X\times Y$ follows and is not added.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Proposition 2.2, p. 234 (third bullet)

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **`f` is continuously differentiable on `X × Y`, convex in `x ∈ X` and concave in `y ∈ Y`,
with partial gradients `fx`, `fy`.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Proposition 2.2, p. 234: "F(z) ≡ F(x, y) = [f′x(x, y); −f′y(x, y)] for a continuously
differentiable function f(x, y) : X × Y → R, which is convex in x ∈ X and is concave in y ∈ Y".

`IsSmoothConvexConcave X Y f fx fy` says: for `x ∈ X`, `y ∈ Y`, `fx (x, y)` is a gradient of
`f(·, y)` at `x` within `X` and `fy (x, y)` a gradient of `f(x, ·)` at `y` within `Y`; `fx` and
`fy` are continuous on `X × Y`; `f(·, y)` is convex on `X` for each `y ∈ Y`; and `f(x, ·)` is
concave on `Y` for each `x ∈ X`.

**Formalization Note.** "Continuously differentiable on `X × Y`" is encoded by partial
gradients within `X` and `Y` that are jointly continuous on `X × Y`; no open set or interior
point is required. Joint continuity of `f` on `X × Y` follows from these clauses and is not
added. -/
def IsSmoothConvexConcave {Ex Ey : Type*} [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex]
    [CompleteSpace Ex] [NormedAddCommGroup Ey] [InnerProductSpace ℝ Ey] [CompleteSpace Ey]
    (X : Set Ex) (Y : Set Ey) (f : Ex × Ey → ℝ) (fx : Ex × Ey → Ex) (fy : Ex × Ey → Ey) :
    Prop :=
  (∀ x ∈ X, ∀ y ∈ Y, HasGradientWithinAt (fun x' => f (x', y)) (fx (x, y)) X x) ∧
    (∀ x ∈ X, ∀ y ∈ Y, HasGradientWithinAt (fun y' => f (x, y')) (fy (x, y)) Y y) ∧
    ContinuousOn fx (X ×ˢ Y) ∧ ContinuousOn fy (X ×ˢ Y) ∧
    (∀ y ∈ Y, ConvexOn ℝ X (fun x => f (x, y))) ∧
    (∀ x ∈ X, ConcaveOn ℝ Y (fun y => f (x, y)))

end NemirovskiProx


