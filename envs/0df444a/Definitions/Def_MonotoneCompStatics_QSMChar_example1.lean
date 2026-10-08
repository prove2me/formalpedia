-- Prove2me | Definitions.Def_MonotoneCompStatics_QSMChar_example1
-- name    : MonotoneCompStatics_QSMChar_example1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:29.605926+00:00
-- url     : https://prove2.me/theorems/e1490301-99d8-42d8-9244-01d6ba5421f6
-- title:
--   The tabulated function of Example 1 on {0,1} × {0,1,2,3} (Milgrom–Shannon, p. 165)
-- statement:
--   Let $X = \{0, 1\} \times \{0, 1, 2, 3\}$, ordered componentwise: $(x, y) \le (x', y')$ iff $x \le x'$ and $y \le y'$. This is a lattice, with join and meet taken coordinatewise as max and min. Example 1 of Milgrom and Shannon is the function $f : X \to \mathbb{R}$ given by the table
--
--   | $x \backslash y$ | 0 | 1 | 2 | 3 |
--   |---|---|---|---|---|
--   | 0 | 1 | 2 | 2 | 1 |
--   | 1 | 3 | 4 | 5 | 3 |
--
--   that is,
--
--   $$
--   f(0, \cdot) = (1, 2, 2, 1), \qquad f(1, \cdot) = (3, 4, 5, 3).
--   $$
--
--   The paper uses it to show that a quasisupermodular function need not be supermodularizable.
--
--   **Formalization Note** The domain is `Fin 2 × Fin 4` with Mathlib's product order, which is the componentwise order of the page; the row index is the first coordinate $x$ and the column index the second coordinate $y$.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 165 (PDF p. 10), Example 1 (table)

import Mathlib

namespace MonotoneCompStatics.QSMChar

/-- The tabulated function of Example 1 (Milgrom–Shannon 1994, p. 165) on the lattice
`{0, 1} × {0, 1, 2, 3}` with the componentwise (product) order: row `x`, column `y`,
`f(0, ·) = (1, 2, 2, 1)` and `f(1, ·) = (3, 4, 5, 3)`. -/
def example1 : Fin 2 × Fin 4 → ℝ := fun p => ![![1, 2, 2, 1], ![3, 4, 5, 3]] p.1 p.2

end MonotoneCompStatics.QSMChar


