-- Prove2me | Definitions.Def_OddPermSum_Evaluation_orderedMinor
-- name    : OddPermSum_Evaluation_orderedMinor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:10:22.834032+00:00
-- url     : https://prove2.me/theorems/605bb9c3-1e67-4a54-9e78-eccee399191a
-- title:
--   Minors in inherited index order
-- statement:
--   If $I,J\subseteq\mathrm{Fin}(n)$ have the same cardinality $r$, their increasing enumerations define
--
--   $$\det A[I,J]=\det\big(A_{I_a,J_b}\big)_{a,b\in\mathrm{Fin}(r)}.$$
--
--   The complementary minor deletes rows $i,j$ and columns $k,l$ and uses these inherited orders. Its determinant at order zero is one. For unequal remaining cardinalities the auxiliary function returns zero; the source sums only use distinct deleted rows and columns, so this branch is never used there.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 5, submatrix conventions; p. 6, Eq. (3.1)

import Mathlib

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- A square minor, with both finite index sets enumerated in their inherited order. -/
noncomputable def orderedMinor {R : Type*} [CommRing R] {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n))
    (hI : I.card = r) (hJ : J.card = r) : R :=
  Matrix.det (A.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ))

/-- Complementary two-row/two-column determinant. Unequal remaining cardinalities give zero;
only distinct deleted rows and columns occur in the source identity. -/
noncomputable def complementaryMinor {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i j k l : Fin n) : R :=
  let I : Finset (Fin n) := Finset.univ \ {i, j}
  let J : Finset (Fin n) := Finset.univ \ {k, l}
  if h : J.card = I.card then orderedMinor A I J rfl h else 0

end OddPermSum.Evaluation


