-- Prove2me | Definitions.Def_WhitneyMatroid_Binary_IsMatroidOf
-- name    : WhitneyMatroid_Binary_IsMatroidOf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:43:24.661216+00:00
-- url     : https://prove2.me/theorems/e73814a3-bd18-4771-9eb5-9957ccbcc219
-- title:
--   The matroid corresponding to a matrix of integers mod 2 (Appendix)
-- statement:
--   Let $\mathbf M$ be a matrix whose entries are integers mod 2, with columns $C_e$ indexed by a set of elements $e$. A family of columns $C_{i_1}, \dots, C_{i_p}$ is **independent (mod 2)** if there are no integers $\alpha_{i_1}, \dots, \alpha_{i_p}$, not all $\equiv 0 \pmod 2$, with
--
--   $$\alpha_{i_1} C_{i_1} + \dots + \alpha_{i_p} C_{i_p} \equiv 0 \pmod 2,$$
--
--   that is, if no non-null subset of the columns sums to the zero column mod 2. Two equal columns with different indices are therefore dependent.
--
--   A matroid $M$ is **the matroid corresponding to** $\mathbf M$ when its elements are exactly the column indices and a set of elements is independent in $M$ exactly when the corresponding columns are independent (mod 2). Since bases, circuits, rank and nullity of a matroid are all determined by its independent sets, this makes all of these notions in $M$ agree with the corresponding notions (mod 2) for the columns of $\mathbf M$.
--
--   **Formalization Note** The matrix is `A : Matrix m α (ZMod 2)`; its columns are the rows of `A.transpose`, and independence (mod 2) is Mathlib's `LinearIndepOn (ZMod 2) A.transpose S` (linear independence of the indexed family of columns in `S`; over `ZMod 2` the coefficients are $0$ or $1$, so this is exactly Whitney's condition). The predicate also requires the ground set of `M` to be all of `α`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 532, Appendix: matrices of integers mod 2, (A.2), independence (mod 2), the matroid M corresponding to C₁, ⋯, Cₙ

import Mathlib

namespace WhitneyMatroid.Binary

/-- The matroid corresponding to a matrix of integers mod 2 (Appendix, p. 532). Let
`A` be a matrix over `ZMod 2` with rows indexed by `m` and columns `C_e` indexed by `α`
(`C_e` is row `e` of the transpose `A.transpose`). Columns `C_{i₁}, …, C_{i_p}` are *independent (mod 2)*
when no non-null subset of them sums to `0` (mod 2), i.e. they are linearly independent over
`ZMod 2` as an indexed family (two equal columns are dependent). `M` is the matroid of `A` when its
elements are exactly the column indices and its independent sets are exactly the sets of
columns independent (mod 2). -/
def IsMatroidOf {α m : Type*} (M : Matroid α) (A : Matrix m α (ZMod 2)) : Prop :=
  M.E = Set.univ ∧ ∀ S : Set α, M.Indep S ↔ LinearIndepOn (ZMod 2) A.transpose S

end WhitneyMatroid.Binary


