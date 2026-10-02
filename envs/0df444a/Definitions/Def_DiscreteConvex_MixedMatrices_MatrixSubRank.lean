-- Prove2me | Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
-- name    : DiscreteConvex_MixedMatrices_MatrixSubRank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:36:40.49983+00:00
-- url     : https://prove2.me/theorems/1c4da409-a594-4170-928a-8a003fe2bf55
-- title:
--   Rank of a submatrix $M[I,J]$
-- statement:
--   The rank of the submatrix $M[I,J]$ of $M$ with row indices in $I \subseteq R$ and column indices in $J \subseteq C$ (the book's notation `A[I,J]`, p.357).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.357

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.357 (the submatrix notation `A[I,J]` and its
rank, used throughout section 12.3), in `DiscreteConvex.MixedMatrices`.
-/

namespace DiscreteConvex.MixedMatrices

/-- The rank of the submatrix `M[I,J]` of `M : Matrix R C 𝔽` with row indices in `I ⊆ R` and
column indices in `J ⊆ C`. -/
noncomputable def MatrixSubRank {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽]
    (M : Matrix R C 𝔽) (I : Finset R) (J : Finset C) : ℕ :=
  (M.submatrix ((↑) : I → R) ((↑) : J → C)).rank

end DiscreteConvex.MixedMatrices


