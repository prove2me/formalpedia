-- Prove2me | Definitions.Def_MagicSquaresMostPerfect
-- name    : MagicSquaresMostPerfect
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:58:02.374188+00:00
-- url     : https://prove2.me/theorems/1d501cfa-7208-4653-b5fe-8ead53e0beb8
-- title:
--   Most-perfect squares
-- statement:
--   **Most-perfect squares.**
--
--   A square of doubly even order $n$ is *most-perfect* with constant $c$ when
--
--   1. every $2\times2$ block, including the four wrapping blocks at the corners, sums to
--      $c$; and
--   2. any two entries $n/2$ apart along a diagonal — major or broken — sum to $c$.
--
--   These are the two conditions used by Ollerenshaw and Brée to single out the one class
--   of magic squares that has been *completely enumerated*. For a normal square of order
--   $n$ with entries $1,\dots,n^{2}$ the classical constant is
--
--   $$c = 2(n^{2}+1),$$
--
--   and the two conditions force the square to be pandiagonal magic and force
--   $4 \mid n$. The number of such squares in the Frénicle standard form is $48$ for
--   $n=4$, $368\,640$ for $n=8$ and $22\,345\,347\,200$ for $n=12$ (OEIS A051235); the
--   general count is a formula involving a double sum over the exponents in the prime
--   factorization of $n$.
--
--   **Why one family of conditions suffices.** For even $n$, putting $h=n/2$ we have
--   $h \equiv -h \pmod n$, so stepping $h$ columns to the right is the same as stepping
--   $h$ columns to the left. The two "diagonal directions" therefore collapse into a
--   single condition, which is also why most-perfect squares are reversible.
--
--   **Formalization Note** As with `IsCompact`, the definition carries the constant `c`
--   instead of hard-coding the classical value $2(n^{2}+1)$, so that the consequences —
--   that a most-perfect square is pandiagonal magic, and that its order is divisible by
--   four — can be stated and proved separately. The diagonal step is written
--   `⟨n / 2 % n, _⟩` so that the definition is well formed for every `n ≥ 1`; the theorem
--   that `4 ∣ n` is what excludes the orders the classical theory does not cover.
-- source:
--   K. Ollerenshaw and D. S. Brée, Most-perfect Pan-diagonal Magic Squares: Their Construction and Enumeration, Institute of Mathematics and its Applications, Southend-on-Sea, 1998; OEIS A051235.

import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

/-!
# Most-perfect squares

A **most-perfect** square of doubly even order `n` is one in which

1. every `2 × 2` block — including the four wrapping blocks at the corners — sums to a
   fixed constant `c`, and
2. any two entries `n / 2` apart along a diagonal (major or broken) are complementary,
   i.e. sum to `c`.

These two conditions are the ones used by Ollerenshaw and Brée, *Most-perfect
pan-diagonal magic squares: their construction and enumeration* (IMA, 1998), to
single out the unique class of magic squares that has been completely enumerated:
they force the square to be pandiagonal magic, and they force `n` to be a multiple of
four. For a normal square of order `n` with entries `1, …, n²` the constant is
`c = 2 (n² + 1)` (equivalently `2 (n² - 1)` for entries `0, …, n² - 1`); the number of
such squares in the Frénicle standard form is `48` for `n = 4`, `368640` for `n = 8`
and `22345347200` for `n = 12` (OEIS A051235).

Note that for even `n` the two "diagonal directions" collapse into one condition:
with `h = n / 2` we have `h ≡ -h (mod n)`, so moving `h` steps down and `h` steps left
is the same as moving `h` steps down and `h` steps right, and a single family of
conditions covers the descending and the ascending diagonals alike. That is also why
most-perfect squares are reversible.

This module provides the predicate only. Like `IsCompact`, it carries a constant `c`
rather than fixing the classical value, so that the theorems derived from it (that a
most-perfect square is pandiagonal magic, and that `n` must be divisible by four) can
be stated separately.
-/

namespace MagicSquares

variable {n : ℕ} {α : Type*}

/-- A square is **most-perfect** with constant `c` when every `2 × 2` block (including
the wrapping ones) sums to `c`, and any two cells `n / 2` apart along a diagonal sum
to `c`.

Because `n / 2 ≡ -n / 2 (mod n)` for even `n`, the single family of conditions on
`(i + n/2, j + n/2)` covers both diagonal directions. For odd `n` the definition is
still well formed but the classical theory does not apply — the companion theorem
that a most-perfect square must have `4 ∣ n` is what rules those out. -/
def IsMostPerfect [NeZero n] [AddCommMonoid α] (M : Square n α) (c : α) : Prop :=
  letI := Fin.instAddMonoidWithOne n
  (∀ i j : Fin n, M i j + M i (j + 1) + M (i + 1) j + M (i + 1) (j + 1) = c) ∧
    (∀ i j : Fin n,
      M i j + M (i + ⟨n / 2 % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩)
          (j + ⟨n / 2 % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩) = c)

end MagicSquares


