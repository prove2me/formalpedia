-- Prove2me | Definitions.Def_BddExp3SUM_ThinProduct
-- name    : BddExp3SUM_ThinProduct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:33.713787+00:00
-- url     : https://prove2.me/theorems/0ba0af35-882e-48c2-99f0-ec5a8a3a0182
-- title:
--   Prescribed entries of a thin matrix product, as a problem on the published word RAM
-- statement:
--   An instance of size $N$ consists of $X\in\mathbb Z^{N\times D}$, $Y\in\mathbb Z^{D\times N}$, and $w$ prescribed positions $(i_a,j_a)$. The required output is the list of entries $(XY)_{i_a,j_a}$, $a<w$, in the cells after the input, and the program must accept.
--
--   This is the problem solved by Alman and Vassilevska Williams's selected-entry thin-matrix algorithm, which the paper uses as a cited theorem. It is an `EndStatement.Problem`, so a solution is a program of the same machine as the goal.
--
--   **Formalization Note** The words are $D$, $w$, $X$ and $Y$ row by row, then the rows and the columns of the positions. $N$ is in cell $0$, as `EndStatement.Problem.SolvedBy` does.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 7, p.6

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

namespace BddExp3SUM

/-!
# Selected entries of a thin matrix product, as a problem on the published word RAM

Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 7, p.6, citing
Alman and Vassilevska Williams, arXiv:2610.06783v1, Corollary 26.

**Formalization Note.** The size parameter is `N` (in cell `0`, as `EndStatement.Problem.SolvedBy` does).
The input is `D`, `w`, then `X` and `Y` row by row, then the row and the column of each of the `w`
prescribed positions. The output cells hold the prescribed entries of `XY` in order. Every instance
is to be accepted (`yes` keeps its default `True`).
-/

/-- `X ∈ Z^{N×D}`, `Y ∈ Z^{D×N}` and `w` prescribed positions. -/
structure ThinInstance (N : ℕ) where
  /-- the thin dimension -/
  D : ℕ
  /-- the number of prescribed positions -/
  w : ℕ
  /-- the left matrix -/
  X : Fin N → Fin D → ℤ
  /-- the right matrix -/
  Y : Fin D → Fin N → ℤ
  /-- the rows of the prescribed positions -/
  wi : Fin w → Fin N
  /-- the columns of the prescribed positions -/
  wj : Fin w → Fin N

/-- The prescribed entries problem. -/
def ThinProduct : EndStatement.Problem where
  Instance N := ThinInstance N
  input x :=
    (x.D : ℤ) :: (x.w : ℤ) ::
      ((List.ofFn fun i => List.ofFn fun t => x.X i t).flatten ++
        (List.ofFn fun t => List.ofFn fun j => x.Y t j).flatten ++
        (List.ofFn fun a => ((x.wi a).val : ℤ)) ++ (List.ofFn fun a => ((x.wj a).val : ℤ)))
  output x out := ∀ a : Fin x.w, out a.val = ∑ t, x.X (x.wi a) t * x.Y t (x.wj a)

end BddExp3SUM


