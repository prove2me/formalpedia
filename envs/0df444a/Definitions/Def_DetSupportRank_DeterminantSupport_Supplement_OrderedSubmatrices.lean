-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_OrderedSubmatrices
-- name    : DetSupportRank_DeterminantSupport_Supplement_OrderedSubmatrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:05:21.925204+00:00
-- url     : https://prove2.me/theorems/a0fcc1c7-3e87-42c4-a1bb-fb37662c5fe8
-- title:
--   Increasingly ordered submatrices and their determinants
-- statement:
--   For a matrix $A$ and finite row and column subsets $I,J$, use their increasing enumerations to form $A_{I,J}$. When the cardinalities agree, its determinant is
--   $$\det(A_{I,J}).$$
--   The empty square minor has determinant one. The helper returns zero for unequal sizes, where a determinant is undefined in the source; no theorem in this supplement uses that extension. This fixes every minor sign and makes the same convention available over scalar and polynomial coefficient rings.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §4.2, submatrix convention, p. 10 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Mathlib

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Increasing enumeration of both row and column subsets; §4.2, p.10. -/
def orderedSubmatrix {R : Type*} {a b : ℕ} (A : Matrix (Fin a) (Fin b) R)
    (I : Finset (Fin a)) (J : Finset (Fin b)) : Matrix (Fin I.card) (Fin J.card) R :=
  A.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin rfl)

/-- Determinant of an ordered square minor. The extension to unequal sizes is zero. -/
def determinantMinor {R : Type*} [CommRing R] {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) R) (I : Finset (Fin a)) (J : Finset (Fin b)) : R :=
  if h : J.card = I.card then
    Matrix.det (A.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h))
  else 0
end DetSupportRank.DeterminantSupport.Supplement


