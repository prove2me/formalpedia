-- Prove2me | Definitions.Def_PriceRobust_Stability_ZPMatrix
-- name    : PriceRobust_Stability_ZPMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:29.148465+00:00
-- url     : https://prove2.me/theorems/09cf7332-6021-4bfb-b4f5-f904b7a076d6
-- title:
--   Definitions B.1–B.3, Appendix p. 6 — Z-matrices, P-matrices and ZP-matrices
-- statement:
--   Let $A$ be a real square matrix indexed by a finite set $n$.
--
--   1. $A$ is a **Z-matrix** if all its off-diagonal entries are non-positive: $A_{lm}\le 0$ for $l\ne m$.
--   2. $A$ is a **P-matrix** if all its principal minors are positive: for every nonempty $S\subseteq n$, $\det A_{S,S}>0$, where $A_{S,S}$ is the principal submatrix with rows and columns in $S$.
--   3. $A$ is a **ZP-matrix** if it is both a Z-matrix and a P-matrix.
--
--   ZP-matrices are what Horn and Johnson call nonsingular M-matrices. They supply the matrix-analytic facts (Lemma B.1) behind the contraction property of the robust best-response map: nonnegativity of inverses, Schur complements, and spectral-radius bounds.
--
--   **Formalization Note** A P-matrix need not be symmetric. Principal submatrices are taken by restricting rows and columns to the subtype of a `Finset`, so no ordering of the indices is imposed.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), Online Appendix p. 6 (PDF 26), Definitions B.1, B.2, B.3

import Mathlib

namespace PriceRobust.Stability

/-- Definition B.1 (Appendix p. 6): a square matrix whose off-diagonal entries are
non-positive is a Z-matrix. -/
def IsZMatrix {n : Type*} (A : Matrix n n ℝ) : Prop :=
  ∀ l m, l ≠ m → A l m ≤ 0

/-- Definition B.2 (Appendix p. 6): a square matrix all of whose principal minors are
positive is a P-matrix. The principal minor on a nonempty index set `S` is the
determinant of the principal submatrix `A_{S,S}`. -/
def IsPMatrix {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  ∀ S : Finset n, S.Nonempty →
    0 < (A.submatrix (fun x : S => (x : n)) (fun x : S => (x : n))).det

/-- Definition B.3 (Appendix p. 6): a ZP-matrix is a matrix that is both a Z-matrix and
a P-matrix. -/
def IsZPMatrix {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  IsZMatrix A ∧ IsPMatrix A

end PriceRobust.Stability


