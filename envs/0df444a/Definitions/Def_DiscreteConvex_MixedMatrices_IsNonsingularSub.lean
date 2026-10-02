-- Prove2me | Definitions.Def_DiscreteConvex_MixedMatrices_IsNonsingularSub
-- name    : DiscreteConvex_MixedMatrices_IsNonsingularSub
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:47:42.239562+00:00
-- url     : https://prove2.me/theorems/4a162cf6-7ff3-49ad-bb90-76c94520686b
-- title:
--   Nonsingularity of a submatrix
-- statement:
--   The submatrix $M[I,J]$ is **nonsingular**: $I$ and $J$ have the same (finite) size and $M[I,J]$ has full rank.
--
--   **Formalization Note.** This is the standard restatement of nonsingularity via rank, used because $I \subseteq R$ and $J \subseteq C$ are (potentially) different types even when $|I|=|J|$, so `Matrix.det` (which needs a single square-matrix index type) is not directly available; for a genuinely square matrix (same index type, full rank) this coincides with the usual notion.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357, Proposition 12.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357, Proposition 12.6

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.357, Proposition 12.6: nonsingularity of a
submatrix, in `DiscreteConvex.MixedMatrices`.
-/

namespace DiscreteConvex.MixedMatrices

/-- The submatrix `M[I,J]` is **nonsingular**: `I` and `J` have the same (finite) size and
`M[I,J]` has full rank. Standard restatement of nonsingularity via rank, used here because
`I : Finset R` and `J : Finset C` are (potentially) different types even when `I.card = J.card`,
so `Matrix.det` (which needs a single square-matrix index type) is not directly available; for a
genuinely square matrix (same index type, full rank) this coincides with the usual notion. -/
def IsNonsingularSub {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽] (M : Matrix R C 𝔽)
    (I : Finset R) (J : Finset C) : Prop :=
  I.card = J.card ∧ MatrixSubRank M I J = I.card

end DiscreteConvex.MixedMatrices


