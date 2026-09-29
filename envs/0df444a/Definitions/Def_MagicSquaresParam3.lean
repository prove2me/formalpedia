-- Prove2me | Definitions.Def_MagicSquaresParam3
-- name    : MagicSquaresParam3
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-16T14:13:15.863108+00:00
-- url     : https://prove2.me/theorems/68eaae9b-d759-4a2a-83f6-741ecdbca5f8
-- title:
--   MacMahon parametrization of 3x3 magic squares
-- statement:
--   The MacMahon parametrization of $3 \times 3$ magic squares.
--
--   Let $M$ be a $3\times3$ array of nonnegative integers whose three rows, three
--   columns and two main diagonals all sum to $s = 3e$. MacMahon's centre identity
--   gives $M_{11} = e$, and then the eight line identities force
--
--   $$M \;=\; \begin{pmatrix}
--   a & 3e-a-c & c \\
--   e+c-a & e & e+a-c \\
--   2e-c & a+c-e & 2e-a
--   \end{pmatrix},
--   \qquad a = M_{00},\; c = M_{02}.$$
--
--   So the square is determined by the pair $(a,c)$, and all nine entries are
--   nonnegative precisely when
--
--   $$e \le a + c \le 3e, \qquad a \le e + c, \qquad c \le e + a .$$
--
--   These inequalities imply $0 \le a, c \le 2e$: adding $a + c \le 3e$ to
--   $a \le e + c$ yields $2a \le 4e$, and symmetrically for $c$. Substituting
--   $p = a - e$, $q = c - e$, the four inequalities become $|p+q| \le e$ and
--   $|p-q| \le e$, equivalently $|p| + |q| \le e$; hence the admissible pairs are in
--   bijection with the $\ell_{1}$ ball of radius $e$ in $\mathbb{Z}^{2}$, which has
--   $$1 + 4\sum_{k=1}^{e} k \;=\; 2e^{2} + 2e + 1$$
--   lattice points. This is MacMahon's count $M_{3}(3e) = 2e^{2} + 2e + 1$.
--
--   **Formalization Note** `mkMagic3 e a c` builds the array above using truncated
--   natural-number subtraction; the row/column/diagonal identities only hold under
--   the admissibility inequalities, which are collected in `IsParam3 e a c`.
--   `paramSet e` is the finite set of admissible pairs, searched inside the lossless
--   box $[0,2e] \times [0,2e]$, and `paramCount e` is its cardinality. Both
--   `paramSet` and `paramCount` are `noncomputable` because membership in `paramSet`
--   involves a decidable proposition.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1915); see also G. Xin, Constructing all magic squares of order three, Electron. J. Combin. (2008), and Beck-Cohen-Cuomo-Gribelyuk, Amer. Math. Monthly 110 (2003).

import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

/-!
# Magic squares of order three: the MacMahon parametrization

This module sets up the classical parametrization of $3 \times 3$ magic squares
that underlies MacMahon's count
$$M_{3}(3e) = 2e^{2} + 2e + 1 .$$

Let $M$ be a $3 \times 3$ magic square with nonnegative integer entries and line
sum $s = 3e$. By `center_of_order_three` the centre is $e$. Putting
$a = M_{00}$ and $c = M_{02}$ and chasing the eight line identities gives

$$M \;=\; \begin{pmatrix}
a & 3e-a-c & c \\
e+c-a & e & e+a-c \\
2e-c & a+c-e & 2e-a
\end{pmatrix}$$

so the square is completely determined by the pair $(a, c)$. All nine entries are
nonnegative exactly when

$$e \le a + c \le 3e, \qquad a \le e + c, \qquad c \le e + a,$$

and these inequalities in turn force $0 \le a, c \le 2e$ (add $a + c \le 3e$ to
$a \le e + c$ to get $2a \le 4e$, and symmetrically). Writing $p = a - e$ and
$q = c - e$, the four inequalities say $|p+q| \le e$ and $|p-q| \le e$, i.e.
$|p| + |q| \le e$; so the parameter set is in bijection with the $\ell_{1}$ ball
of radius $e$ in $\mathbb{Z}^{2}$, which contains
$1 + 4\sum_{k=1}^{e} k = 2e^{2} + 2e + 1$ lattice points.

The module provides the parametrization `mkMagic3`, the finite parameter set
`paramSet`, and the counting function `paramCount`. The two substantive
statements — that `mkMagic3` sets up a bijection onto the magic squares, and that
`paramCount e = 2e^2 + 2e + 1` — are submitted separately as theorems.
-/

namespace MagicSquares

/-- The canonical $3 \times 3$ array attached to a line sum `3 * e` and two
parameters `a`, `c`, as in the module docstring. Entries are natural numbers, so
the subtractions are truncated; the row/column/diagonal identities hold under the
admissibility inequalities recorded in `paramSet`. -/
def mkMagic3 (e a c : ℕ) : Square 3 ℕ :=
  ![![a, 3 * e - a - c, c],
    ![e + c - a, e, e + a - c],
    ![2 * e - c, a + c - e, 2 * e - a]]

noncomputable section

/-- Whether a parameter pair `(a, c)` is admissible for line sum `3 * e`. -/
def IsParam3 (e a c : ℕ) : Prop :=
  e ≤ a + c ∧ a + c ≤ 3 * e ∧ a ≤ e + c ∧ c ≤ e + a

/-- The finite set of admissible parameter pairs. As shown in the module
docstring, admissibility forces `a ≤ 2 * e` and `c ≤ 2 * e`, so searching the
`[0, 2e] × [0, 2e]` box is lossless. -/
def paramSet (e : ℕ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact ((Finset.range (2 * e + 1)).product (Finset.range (2 * e + 1))).filter
      (fun ac => IsParam3 e ac.1 ac.2)

/-- The number of admissible parameter pairs for line sum `3 * e`. -/
def paramCount (e : ℕ) : ℕ := (paramSet e).card

end

end MagicSquares


