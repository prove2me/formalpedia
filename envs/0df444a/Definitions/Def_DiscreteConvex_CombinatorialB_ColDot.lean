-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_ColDot
-- name    : DiscreteConvex_CombinatorialB_ColDot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:20.380523+00:00
-- url     : https://prove2.me/theorems/dd4d8cfd-31b9-41bb-999a-5e3c227a53c5
-- title:
--   Pairing xᵀm_j with a column of M
-- statement:
--   $\mathrm{ColDot}(M,x,j) = x^\top m_j$, the pairing of $x$ with the $j$-th column $m_j$ of $M$ (computed as $(Mx)_j$, valid when $M$ is symmetric).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.69-70.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.69-70

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69-70: `x⊤m_j`, the pairing of `x` with the
`j`-th column `m_j` of a matrix `M`, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- `ColDot M x j = x⊤m_j`, the pairing of `x` with the `j`-th column `m_j` of `M`. For `M`
symmetric this equals `(M.mulVec x) j`, which is how it is computed here (Theorem 2.12 is
stated only for symmetric `M`). -/
def ColDot {V : Type*} [Fintype V] (M : Matrix V V ℝ) (x : V → ℝ) (j : V) : ℝ :=
  M.mulVec x j

end DiscreteConvex.CombinatorialB


