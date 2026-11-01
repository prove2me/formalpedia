-- Prove2me | Definitions.Def_NoSignalPA_cell
-- name    : NoSignalPA_cell
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:44.021082+00:00
-- url     : https://prove2.me/theorems/e74140a9-2c3c-4eba-8caf-bee4a74ec8cd
-- title:
--   Cell of a pair of bits in the layout (3)
-- statement:
--   The paper arranges vectors of $\mathbb R^{16}$ as $4\times4$ tables (3): the rows are indexed by Alice's pair $(a,x)$ in the order $00,10,01,11$ and the columns by Bob's pair $(b,y)$ in the same order. The cell of $(a,x)$ is $a+2x\in\{0,1,2,3\}$.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, eq. (3), p.1

import Mathlib

namespace NoSignalPA

/-- **The cell of a pair of bits in the 4 × 4 layout (3).**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, eq. (3), p. 1 (printed p. 1 has no number; PDF p. 1): the vector `|P_{a,b|x,y}⟩` is arranged
with rows `(a, x) = (0,0), (1,0), (0,1), (1,1)` and columns `(b, y)` in the same order.

`cell a x = a + 2x ∈ {0, 1, 2, 3}` is the row of `(a, x)`, and `cell b y` the column of
`(b, y)`. -/
def cell (a x : Bool) : Fin 4 :=
  ⟨a.toNat + 2 * x.toNat, by cases a <;> cases x <;> decide⟩

end NoSignalPA


