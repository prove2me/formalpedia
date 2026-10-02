-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_KerMat
-- name    : DiscreteConvex_CombinatorialC_KerMat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:40:08.408521+00:00
-- url     : https://prove2.me/theorems/df05b069-44bb-4ade-a165-33c2d855ca4a
-- title:
--   Kernel of a matrix
-- statement:
--   $\ker M=\{x\in\mathbb R^n : Mx=0\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.73, Eq. (2.26).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.73, Eq. (2.26)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.73, Eq. (2.26): the kernel of a matrix, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `ker M = \{x ∈ Rⁿ | Mx = 0\}` (Eq. (2.26)). -/
def KerMat {V : Type*} [Fintype V] (M : Matrix V V ℝ) : Set (V → ℝ) :=
  {x | M.mulVec x = 0}

end DiscreteConvex.CombinatorialC


