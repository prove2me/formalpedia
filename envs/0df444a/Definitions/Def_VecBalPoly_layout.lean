-- Prove2me | Definitions.Def_VecBalPoly_layout
-- name    : VecBalPoly_layout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:09:57.966823+00:00
-- url     : https://prove2.me/theorems/882696b3-1c2f-4edb-bfc9-fc6a11772af1
-- title:
--   Input layout of an $m\times n$ real matrix
-- statement:
--   The machine input for a matrix $A\in\mathbb R^{m\times n}$ is the list of reals
--   $$(m,\ n,\ a_{11},\dots,a_{1n},\ a_{21},\dots,a_{mn}),$$
--   that is, the dimensions followed by the entries row by row. The output of a program is read from the cells immediately after the input.
--
--   **Formalization Note** The paper fixes no layout. The index cells of the published machine start at $0$, so a program reads $m$ and $n$ by a counting loop in $O(m+n)$ steps.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Theorem 1.1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM

namespace VecBalPoly

/-- **The machine's input for a matrix.** The reals `m, n`, then the entries of
`A ∈ ℝ^{m×n}` row by row.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Theorem 1.1, p.1 (PDF p.2): "given any m, n ≥ 1 and A ∈ ℝ^{m×n}".

**Formalization Note** The paper fixes no layout. Index cells of the published machine start at
`0`, so a program reads `m, n` by a counting loop (step an index cell and a real cell together
until `rblt` says the real cell has reached the input), in `O(m + n)` steps. The output is read
from the cells right after the input. -/
noncomputable def layout (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) : List ℝ :=
  [(m : ℝ), (n : ℝ)] ++ MatMulTimeLP.matToList A

end VecBalPoly


