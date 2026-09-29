-- Prove2me | Definitions.Def_MagicSquaresSpecial3
-- name    : MagicSquaresSpecial3
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:02:17.036993+00:00
-- url     : https://prove2.me/theorems/dc7c7ce9-2547-4cd2-9592-2974f777ff2a
-- title:
--   Special classes of order-three magic squares: panmagic and symmetric
-- statement:
--   The two classical special classes of $3\times3$ magic squares, and the explicit shapes they take.
--
--   A square is **panmagic** (pandiagonal) when the semi-magic conditions hold and *every* broken diagonal in both directions has the line sum; it is **symmetric** when it equals its own transpose.
--
--   For order three both classes are determined by a single parameter:
--
--   * `constSquare3 e` is the array all of whose entries are `e`, read over `Fin (3*e+1)` -- the ambient type of the counting functions at line sum `3*e`. It is the unique panmagic square of line sum `3*e`.
--   * `symmMagic3 e a` is the symmetric shape $\begin{pmatrix} a & 2e-a & e \\ 2e-a & e & a \\ e & a & 2e-a \end{pmatrix}$, which is symmetric for every `a` and a square of nonnegative integers of line sum `3*e` exactly when `a <= 2*e`.
--   * `symmParamSet e` is the corresponding admissible set of corner parameters, the `2*e+1` values `0, ..., 2*e`, and `symmParamCount e` its cardinality.
--
--   The counting theorems built on these shapes -- that there is exactly one panmagic square and exactly `2*e+1` symmetric squares of line sum `3*e` -- are submitted separately.
-- source:
--   P. A. MacMahon, Combinatory Analysis, Vol. II, Cambridge University Press, 1916; M. Beck, T. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; W. S. Andrews, Magic Squares and Cubes, 2nd ed., Dover, 1960.

import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

/-!
# Special classes of order-three magic squares

Missions I--III handled *counting* and *classifying* order-three magic squares.
This module sets up the two classical special classes that are singled out by
extra symmetry requirements:

* **panmagic (pandiagonal)** squares, where *every* broken diagonal -- not just
  the two main ones -- has the magic sum;
* **symmetric** squares, where the array equals its own transpose.

For order three both classes turn out to have a completely explicit shape. Let
`M` be a `3 × 3` array of nonnegative integers with line sum `3 * e`, written

$$M=\begin{pmatrix} a & b & c \\ d & e_{11} & f \\ g & h & i \end{pmatrix}.$$

*Panmagic.* Besides the twelve line sums there is nothing left to choose: the
broken diagonal `b + f + g` and the broken anti-diagonal `b + d + i` together
with the rows and columns force `a = b = c = d = e_{11} = f = g = h = i = e`.
So `constSquare3 e` -- the array all of whose entries are `e` -- is the only
panmagic square of line sum `3 * e`.

*Symmetric.* Symmetry identifies `b = d`, `c = g` and `f = h`, so only the five
cells `a, b, c, e_{11}, i` remain free; the anti-diagonal reads
`2 c + e_{11} = 3 e`. The four remaining line sums then give

$$\mathrm{symmMagic3}(e,a)=\begin{pmatrix}
a & 2e-a & e \\ 2e-a & e & a \\ e & a & 2e-a \end{pmatrix},$$

an array which is symmetric for every `a`, and admissible exactly when
`0 ≤ a ≤ 2 e`, i.e. for the `2 e + 1` values collected in `symmParamSet e`.

The two counting theorems built on these shapes are submitted separately.
-/

namespace MagicSquares

/-- The constant `3 × 3` array with every entry equal to `e`, read as an array
over `Fin (3 * e + 1)` -- the ambient type of the counting functions at line
sum `3 * e`. -/
def constSquare3 (e : ℕ) : Square 3 (Fin (3 * e + 1)) :=
  fun _ _ => ⟨e, by omega⟩

/-- The symmetric `3 × 3` shape of line sum `3 * e` attached to the free corner
parameter `a`. It is symmetric for every `a`; it is a square of nonnegative
integers of line sum `3 * e` exactly when `a ≤ 2 * e`. -/
def symmMagic3 (e a : ℕ) : Square 3 ℕ :=
  ![![a, 2 * e - a, e],
    ![2 * e - a, e, a],
    ![e, a, 2 * e - a]]

noncomputable section

/-- The admissible corner parameters of the symmetric family of line sum
`3 * e`, namely the `2 * e + 1` values `0, …, 2 * e`. -/
def symmParamSet (e : ℕ) : Finset ℕ := Finset.range (2 * e + 1)

/-- The number of admissible corner parameters of the symmetric family. -/
def symmParamCount (e : ℕ) : ℕ := (symmParamSet e).card

end

end MagicSquares


