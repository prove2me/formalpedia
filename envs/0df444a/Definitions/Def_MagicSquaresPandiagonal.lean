-- Prove2me | Definitions.Def_MagicSquaresPandiagonal
-- name    : MagicSquaresPandiagonal
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:57:54.941239+00:00
-- url     : https://prove2.me/theorems/95bcf1fc-345e-4db9-ae0c-cc8d9dba9fb2
-- title:
--   Pandiagonal squares: the counting-theory reading
-- statement:
--   **Pandiagonal squares: the counting-theory reading.**
--
--   A $3\times3$ array of nonnegative integers is *pandiagonal* of line sum $s$ when all
--   three rows, all three columns, and the three diagonals **parallel to the main
--   diagonal**, wrapped around (i.e. read cyclically), sum to $s$. Writing $P_{n}(t)$ for
--   the number of pandiagonal squares of order $n$ and line sum $t$, this is the counting
--   function whose structural theory is established by Beck–Cohen–Cuomo–Gribelyuk.
--
--   **This is a different, and weaker, condition than `MagicSquares.IsPanMagic`.** The
--   latter requires *both* families of broken diagonals — descending and ascending — to
--   sum to the line sum, whereas the definition here asks only for the descending family
--   (the one containing the main diagonal) and explicitly does *not* require the
--   anti-diagonal. Consequently a pandiagonal square in this sense need not be magic, and
--   a magic square need not be pandiagonal: for order three the two counts are
--
--   $$P_{3}(t):\quad 1,3,6,10,15,21,28,36,45,55\quad(t=0,\dots,9),$$
--
--   which is $\binom{t+2}{2}=\frac12t^2+\frac32t+1$, against the two-direction count
--   $1$ exactly when $3\mid t$ and $0$ otherwise. Counting against the literature must use
--   this definition, not `panMagicCount`.
--
--   The two counting functions therefore behave quite differently: $P_{3}$ is a
--   degree-two polynomial that never vanishes, so it sits inside the structural statement
--   that $P_{n}$ is a quasi-polynomial of degree $n^{2}-3n+2$.
--
--   **Formalization Note** `pandiagonalSquares` filters arrays over `Fin (t+1)`, which is
--   lossless because every entry of a square of line sum $t$ is at most $t$. The
--   descending broken diagonal of offset $k$ is `brokenDiagSum`, the cells $(i, i+k)$ with
--   the column index read modulo $n$; the main diagonal is the case $k = 0$.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

/-!
# Pandiagonal squares: the counting-theory reading

⚠️ **This notion is weaker than `MagicSquares.IsPanMagic`, and the two are not
comparable.** Read this docstring before using either.

* `IsPanMagic M s` requires **both** families of broken diagonals (descending *and*
  ascending) to sum to `s`.
* `IsPandiagonal M s`, defined here, is the reading used by the counting literature
  (Beck, Cohen, Cuomo and Gribelyuk, *The number of "magic" squares, cubes and
  hypercubes*, Amer. Math. Monthly **110** (2003), 707--717): a **semi-magic** square
  whose diagonals *parallel to the main diagonal*, wrapped around, all sum to the line
  sum. Only one family is asked for, and the anti-diagonal is not — so a pandiagonal
  square in this sense need not be magic, and a magic square need not be pandiagonal.

For order three the difference is stark — the two counts are

| `t` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| `pandiagonalCount 3 t` (this reading) | 1 | 3 | 6 | 10 | 15 | 21 | 28 | 36 | 45 | 55 |
| `panMagicCount 3 t` (both directions) | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 |

The first column is
`(t+2).choose 2 = (t+1)(t+2)/2`, which is BCCG's `P_3(t)`: a degree-two polynomial,
never zero. The second is the constant square only, and vanishes off multiples of
three. Structure behind the first: for `n = 3` every such square is
`M i j = f (i + j)` for a single `f : Fin 3 → ℕ`, and the line sum is
`f 0 + f 1 + f 2` — whence the count is the number of triples of naturals summing
to `t`.

The counting functions satisfying this weaker condition are exactly the ones for
which BCCG's structural theorems (polynomial / quasi-polynomial degrees) are stated,
so this module is what a comparison against that paper should be built on.
-/

namespace MagicSquares

variable {n : ℕ} {α : Type*}

/-- A **pandiagonal square** of line sum `s` in the counting-theory sense: semi-magic,
and every descending broken diagonal sums to `s`.

The descending broken diagonal of offset `k` is the set of cells `(i, i + k)` with the
column index read modulo `n`; for `k = 0` it is the main diagonal, so the main diagonal
is included. The ascending family (which contains the anti-diagonal) is **not**
required — see the module docstring, and compare `IsPanMagic`. -/
def IsPandiagonal [AddCommMonoid α] (M : Square n α) (s : α) : Prop :=
  IsSemiMagic M s ∧ ∀ k : Fin n, brokenDiagSum M k = s

noncomputable section

/-- All pandiagonal squares of order `n` and line sum `t`, in the counting-theory
sense of `IsPandiagonal`. -/
def pandiagonalSquares (n t : ℕ) : Finset (Square n (Fin (t + 1))) :=
  by classical exact Finset.univ.filter fun M => IsPandiagonal (fun i j => (M i j : ℕ)) t

/-- BCCG's `P_n(t)`: the number of pandiagonal squares of order `n` and line sum `t`.

This is *not* `panMagicCount`, which counts the stronger two-direction condition. -/
def pandiagonalCount (n t : ℕ) : ℕ := (pandiagonalSquares n t).card

end

end MagicSquares


