-- Prove2me | Definitions.Def_NemirovskiProx_saddleOp
-- name    : NemirovskiProx_saddleOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:47:19.981853+00:00
-- url     : https://prove2.me/theorems/bb9b0349-f933-418b-9386-dbe80b486a43
-- title:
--   Saddle operator $F=[f'_x;-f'_y]$
-- statement:
--   For maps $f'_x:E_x\times E_y\to E_x$ and $f'_y:E_x\times E_y\to E_y$ (the partial gradients of $f$), the operator on $E=E_x\times E_y$
--   $$F(x,y)=\begin{bmatrix}f'_x(x,y)\\ -f'_y(x,y)\end{bmatrix}.$$
--
--   For convex-concave $f$ this is the monotone operator whose variational inequality on $X\times Y$ is equivalent to the saddle point problem for $f$.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Proposition 2.2, p. 234 (F(z) ≡ F(x, y) = [f′x(x, y); −f′y(x, y)])

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The operator `F(x, y) = [f′_x(x, y); −f′_y(x, y)]` of a saddle point problem.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Proposition 2.2, p. 234: "F(z) ≡ F(x, y) = [f′x(x, y); −f′y(x, y)]".

`saddleOp fx fy (x, y) = (fx (x, y), − fy (x, y))` on `WithLp 2 (Ex × Ey)`, where `fx`, `fy`
are the partial gradients of `f` (see `IsSmoothConvexConcave`). -/
def saddleOp {Ex Ey : Type*} [AddCommGroup Ex] [AddCommGroup Ey]
    (fx : Ex × Ey → Ex) (fy : Ex × Ey → Ey) : WithLp 2 (Ex × Ey) → WithLp 2 (Ex × Ey) :=
  fun z => WithLp.toLp 2 (fx (WithLp.ofLp z), -fy (WithLp.ofLp z))

end NemirovskiProx


