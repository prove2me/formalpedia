-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_Lin2Eq
-- name    : HeilmanMax3Cut_Supplement_Lin2Eq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:04:23.361799+00:00
-- url     : https://prove2.me/theorems/5510e6fc-c9d5-41d6-b2ac-f3e43b45681e
-- title:
--   A two-term equation $x_i-x_j=c \bmod 3$
-- statement:
--   An equation $x_i-x_j=c$ over $\mathbb Z/3$ in variables $x_1,\dots,x_n$, with $i\ne j$ and $c\in\mathbb Z/3$. Theorem 1.5 holds for instances made only of such equations.
--
--   **Formalization Note** Variables are indexed $0,\dots,n-1$; the condition $i\ne j$ excludes the degenerate equation $0=c$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.5, p.4

import Mathlib

namespace HeilmanMax3Cut.Supplement

/-- **A two-term equation `x_i − x_j = c mod 3`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.5, p.4: MAX-2-LIN(3) "asks to
maximize the number of satisfied linear equations among two-term linear equations in the field of
three elements", and "the result holds even when every equation has the form `x_i − x_j = c mod 3`".

`Lin2Eq n` is an equation `x_i − x_j = c` over `ℤ/3` in the variables `x_1, …, x_n`.

**Formalization Note.** Variables are `Fin n` (the paper's `x_1, …, x_n` are `0, …, n − 1`) and
`c ∈ ZMod 3`. `hne` records `i ≠ j`: an equation with `i = j` would read `0 = c` and is not a
two-term equation. Only the difference form is represented; hardness for it is the paper's
strongest clause. -/
structure Lin2Eq (n : ℕ) where
  /-- the first variable `x_i` -/
  i : Fin n
  /-- the second variable `x_j` -/
  j : Fin n
  /-- the right-hand side `c ∈ ℤ/3` -/
  c : ZMod 3
  /-- the two variables are distinct -/
  hne : i ≠ j

end HeilmanMax3Cut.Supplement


