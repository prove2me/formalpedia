-- Prove2me | Definitions.Def_AubinLipschitz_solMap
-- name    : AubinLipschitz_solMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:23.303001+00:00
-- url     : https://prove2.me/theorems/54d560d1-609f-4a08-acb5-f8a04d613401
-- title:
--   §5, (5) — the solution map $F^{-1}(p,y,A)$
-- statement:
--   For proper convex $U:X\to\mathbb R\cup\{+\infty\}$ and $V:Y\to\mathbb R\cup\{+\infty\}$, the **solution map** sends parameters $(p,y,A)\in X^*\times Y\times L(X,Y)$ to the set $F^{-1}(p,y,A)$ of all solutions $(x,q)\in X\times Y^*$ of
--
--   $$
--   p\in\partial U(x)+A^*q,\qquad y\in -Ax+\partial V^*(q).
--   $$
--
--   It is the object whose stability the goal of the mission describes.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (5), p.32

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_AubinLipschitz_invMap
import Definitions.Def_AubinLipschitz_paramMap
import Definitions.Def_AubinLipschitz_subdiffConj
open RockafellarMaxMono.Shared

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (5), p.32: `F⁻¹(p, y, A)` is the set of solutions `(x, q) ∈ X × Y*` of
`p ∈ ∂U(x) + A*q`, `y ∈ −A x + ∂V*(q)`; it is the inverse of the map `F` of (9)–(10), p.33, with
`G = ∂U` and `H⁻¹ = ∂V*`. -/
def solMap {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : X → EReal) (V : Y → EReal) :
    StrongDual ℝ X × Y × (X →L[ℝ] Y) → Set (X × StrongDual ℝ Y) :=
  invMap (paramMap (subdiff U) (subdiffConj V))

end AubinLipschitz


