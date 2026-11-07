-- Prove2me | Definitions.Def_ArgmaxDeFinetti_coeffMat
-- name    : ArgmaxDeFinetti_coeffMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:15.192194+00:00
-- url     : https://prove2.me/theorems/92cfebc3-c09a-4a60-bb9a-92688ae356bb
-- title:
--   Coefficient matrix of a bipartite vector
-- statement:
--   For $z\in\mathcal X\otimes\mathcal Y$ with standard orthonormal bases $(e_i)$, $(f_j)$, the coefficient matrix $Z$ is defined by
--   $$
--   z=\sum_{i,j}Z_{ij}\,e_i\otimes f_j .
--   $$
--   The tensor norms of $z$ are Schatten norms of $Z$ (2.15).
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.3, p.22 (before (2.15))

import Mathlib

open Matrix

namespace ArgmaxDeFinetti

/-- The coefficient matrix `Z` of `z ∈ X ⊗ Y` in the standard orthonormal bases, `z = Σ_{i,j} Z_{ij} e_i ⊗ f_j`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.3, p.22 (before (2.15)). -/
def coeffMat {ι κ : Type} (z : ι × κ → ℂ) : Matrix ι κ ℂ :=
  fun i j => z (i, j)

end ArgmaxDeFinetti


