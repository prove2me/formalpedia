-- Prove2me | Definitions.Def_NemirovskiProx_prodSet
-- name    : NemirovskiProx_prodSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:47:04.505618+00:00
-- url     : https://prove2.me/theorems/2c362963-194f-4d0a-a573-f782ad8aca2d
-- title:
--   Product set $Z=X\times Y$
-- statement:
--   For $X\subset E_x$ and $Y\subset E_y$, the set $Z=X\times Y$ of pairs $(x,y)$ with $x\in X$, $y\in Y$, viewed inside the Euclidean space $E=E_x\times E_y$.
--
--   It is the feasible set of the variational inequality associated with a convex-concave saddle point problem in Proposition 2.2 and Theorem 3.2.
--
--   **Formalization Note** $E_x\times E_y$ is `WithLp 2 (Ex × Ey)`, whose inner product is $\langle x,x'\rangle+\langle y,y'\rangle$.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Proposition 2.2, p. 234 (Z = X × Y)

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The set `Z = X × Y` inside `E = E_x × E_y`.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Proposition 2.2, p. 234: "E = Ex × Ey for Euclidean spaces Ex, Ey, Z = X × Y for convex
compacts X ⊂ Ex, Y ⊂ Ey".

`prodSet X Y` is the set of `z ∈ WithLp 2 (Ex × Ey)` whose first component lies in `X` and
second in `Y`.

**Formalization Note.** `E_x × E_y` is `WithLp 2 (Ex × Ey)`, whose inner product is
`⟨x, x′⟩ + ⟨y, y′⟩`, the Euclidean structure of the product used on p. 236. -/
def prodSet {Ex Ey : Type*} (X : Set Ex) (Y : Set Ey) : Set (WithLp 2 (Ex × Ey)) :=
  {z | (WithLp.ofLp z).1 ∈ X ∧ (WithLp.ofLp z).2 ∈ Y}

end NemirovskiProx


