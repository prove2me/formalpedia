-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_coeffMatrix
-- name    : LoPopescuCC_Dilution_coeffMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:59.987969+00:00
-- url     : https://prove2.me/theorems/50cbf60a-b5ab-4832-a94c-9d5b47be6b9f
-- title:
--   Coefficient matrix of a bipartite vector
-- statement:
--   For a bipartite vector $v$ with amplitudes $v(i,j)$, the coefficient matrix is $M_{ij}=v(i,j)$, with rows indexed by Alice's basis and columns by Bob's. The Schmidt coefficients of $v$ are the nonzero singular values of $M$, so their squares are the nonzero eigenvalues of $MM^\dagger$. When $v$ is normalized, $MM^\dagger$ is the reduced density matrix $\rho^A$.
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, footnote [9], Eq. (11), p. 8

import Mathlib

namespace LoPopescuCC.Dilution

/-- **Coefficient matrix of a bipartite vector** (Lo, Popescu, arXiv:quant-ph/9902045v2, footnote
[9], Eq. (11), p. 8): the matrix `M` with `M_{ij} = v(i, j)`, rows indexed by Alice's basis and
columns by Bob's. The Schmidt coefficients of `v` are the nonzero singular values of `M`, so
their squares are the nonzero eigenvalues of `M Mᴴ`, which is `ρ^A` when `v` is normalized. -/
def coeffMatrix {a b : Type} (v : EuclideanSpace ℂ (a × b)) : Matrix a b ℂ :=
  Matrix.of fun i j => v (i, j)

end LoPopescuCC.Dilution


