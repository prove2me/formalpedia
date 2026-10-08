-- Prove2me | Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf
-- name    : WhitneyMatroid_Fano_IsMatroidOf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:57.656154+00:00
-- url     : https://prove2.me/theorems/dcb2de32-8878-4088-92b1-a70f5668d109
-- title:
--   The matroid of a matrix (§12)
-- statement:
--   Let $K$ be a field and let $\mathbf M=(a_{ij})$ be an $m\times n$ matrix with entries in $K$, whose columns $C_1,\dots,C_n$ are indexed by a finite set $\iota$. Any subset $N$ of the columns forms a matrix, which has a rank $r(N)$. Whitney regards the columns as abstract elements: a matroid $M$ on the ground set $\iota$ **is the matroid of** $\mathbf M$ when every column is an element of $M$ and, for every set $N\subseteq\iota$ of columns,
--
--   $$
--   r_M(N) \;=\; \operatorname{rank}\bigl(\mathbf M[\,\cdot\,,N]\bigr),
--   $$
--
--   the rank of the submatrix of $\mathbf M$ formed by the columns in $N$.
--
--   Equivalently, a set of columns is independent in $M$ exactly when it is linearly independent over $K$, and a base of $M$ is a minimal set of columns in terms of which all remaining columns may be expressed. This is the object through which Whitney compares abstract matroids with matrices: a matroid "corresponds to a matrix" when it is the matroid of that matrix.
--
--   **Formalization Note** Whitney's matrices are real; the definition is stated for an arbitrary field $K$ so that the same predicate also expresses the matrix of integers mod 2 of p. 533. The ground set is the whole column index type, and ranks are Mathlib's extended-natural ranks `M.eRk`, compared with the natural-number rank of the submatrix.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), pp. 524–525, §12

import Mathlib

namespace WhitneyMatroid.Fano

/-- Whitney §12 (pp. 524–525): `M` is the matroid of the `m × n` matrix `A` (entries in a field
`K`, columns indexed by the finite type `ι`). The elements of `M` are the columns of `A` (the
ground set is all of `ι`), and a set `N` of columns has rank `r(N)` equal to the rank of the
submatrix of `A` formed by the columns in `N`. -/
def IsMatroidOf {K : Type*} [Field K] {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matroid ι) (A : Matrix (Fin m) ι K) : Prop :=
  M.E = Set.univ ∧
    ∀ N : Finset ι, M.eRk (N : Set ι) = ((A.submatrix id (fun j : N => (j : ι))).rank : ℕ∞)

end WhitneyMatroid.Fano


