-- Prove2me | Definitions.Def_MagicSquaresNormal3
-- name    : MagicSquaresNormal3
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-17T07:06:07.438261+00:00
-- url     : https://prove2.me/theorems/2581f8bc-149c-4259-b2c6-858f0d62a9b5
-- title:
--   Normal order-three magic squares: the surviving parameter pairs
-- statement:
--   The admissible MacMahon parameter pairs whose order-three square is normal.
--
--   MacMahon's parametrization writes every order-three magic square of line sum
--   $3e$ as $\mathrm{mkMagic3}(e,a,c)$ with $(a,c)$ in the finite set
--   $\mathrm{paramSet}(e)$. A square is **normal** when its nine entries are exactly
--   $1,\dots,9$, each occurring once. For $e = 5$ the line sum is $15$, the magic
--   constant of a normal square of order three.
--
--   `normalParamSet e` is the subset of `paramSet e` consisting of those pairs whose
--   MacMahon square is normal, and `normalParamCount e` is its cardinality. The
--   classification theorem `magic_three_normal_eight` shows
--   $\mathrm{normalParamCount}(5) = 8$, i.e. the Lo Shu square is unique up to the
--   symmetry group of the square.
--
--   The set is declared with `classical`: `IsNormal` is stated using
--   `Function.Injective`, which carries no decidable instance, so the defining
--   `filter` cannot be formed constructively.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1916); W. S. Andrews, Magic Squares and Cubes, 2nd ed., Dover, 1960.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

/-!
# Normal order-three magic squares: the parameter pairs that survive

MacMahon's parametrization writes every order-three magic square of line sum
`3 * e` as `mkMagic3 e a c`, with `(a, c)` in the finite set `paramSet e`. A
square is **normal** when its nine entries are exactly `1, …, 9`, each once
(`IsNormal`).

For `e = 5` the line sum is `15`, the magic constant of a normal square of order
three, and the classification problem is to decide which admissible pairs give a
normal square. `normalParamSet e` collects them.

The set is defined with `classical` because `IsNormal` — being stated with a
`Function.Injective` — carries no decidable instance, so the `filter` cannot be
formed constructively. The classification itself (`magic_three_normal_eight`)
shows that `normalParamSet 5` has exactly eight elements.
-/

namespace MagicSquares

noncomputable section

/-- The admissible parameter pairs whose MacMahon square is normal. -/
def normalParamSet (e : ℕ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (paramSet e).filter fun ac => IsNormal (mkMagic3 e ac.1 ac.2)

/-- The number of admissible parameter pairs giving a normal square. -/
def normalParamCount (e : ℕ) : ℕ := (normalParamSet e).card

end

end MagicSquares


