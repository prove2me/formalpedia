-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_DirDeriv
-- name    : DiscreteConvex_CombinatorialB_DirDeriv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:21.460775+00:00
-- url     : https://prove2.me/theorems/ab194d5a-fcf7-4a28-8e42-fbb4afec1975
-- title:
--   Directional derivative of a quadratic form
-- statement:
--   $\mathrm{DirDeriv}(M,x,d) = x^\top M d$, the closed-form directional derivative $f'(x;d)$ of $f(x)=\tfrac12x^\top Mx$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, proof of Theorem 2.12.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, proof of Theorem 2.12

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.70, proof of Theorem 2.12 (using
`f'(x;d) = x⊤Md`): the directional derivative of the quadratic form `f(x) = (1/2)x⊤Mx`, in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- `DirDeriv M x d = x⊤Md`, the closed-form directional derivative `f'(x;d)` of the quadratic
form `f(x) = (1/2)x⊤Mx` at `x` in direction `d`, as computed in the book's proof of
Theorem 2.12 ((c+) ⇔ (d+)). -/
def DirDeriv {V : Type*} [Fintype V] (M : Matrix V V ℝ) (x d : V → ℝ) : ℝ :=
  dotProduct x (M.mulVec d)

end DiscreteConvex.CombinatorialB


