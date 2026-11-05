-- Prove2me | Definitions.Def_DotySW_Deranged_diagOp
-- name    : DotySW_Deranged_diagOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:25.621208+00:00
-- url     : https://prove2.me/theorems/df6cf1e7-de89-4ca0-80a1-c8d0ade53edc
-- title:
--   The operator of an $(r,s)$-diagram on $V^{r,s}$
-- statement:
--   An $(r,s)$-diagram $D$ acts on $V^{r,s}$ by the matrix whose entry at row $i$, column $j$ is $1$ when the labelling of the vertices of $D$ with $i$ on the top row and $j$ on the bottom row is constant on every edge of $D$, and $0$ otherwise.
--
--   So a vertical edge identifies an input and an output position, a horizontal edge on the bottom row is a contraction, and a horizontal edge on the top row inserts $\sum_m e_m\otimes e_m^*$. This is the action of $\mathcal B^{(n)}_{r+s}$ on $V^{\otimes(r+s)}$ restricted to walled diagrams, as on p. 9.
--
--   **Formalization Note** The top row is the output and the bottom row the input. The identification $V\simeq V^*$ of p. 9 is $e_i\leftrightarrow e_i^*$, so one formula serves all positions.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §2.2, unnumbered, p. 5, and §3.4, unnumbered, p. 9

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Algebra
import Definitions.Def_DotySW_Deranged_Op

namespace DotySW.Deranged

open WalledBrauer.Blocks

/-- **The operator of an `(r, s)`-diagram on `V^{r,s}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §2.2, unnumbered, p. 5, and §3.4, unnumbered, p. 9.

The entry at row `i`, column `j` is `1` when the labelling of the diagram's vertices that puts `i`
on the top row and `j` on the bottom row is constant on every edge of `D`, and `0` otherwise.
This is the Brauer action of `B^{(n)}_{r+s}` on `V^{⊗(r+s)}` restricted to walled diagrams: a
vertical edge is an identification of tensor positions, a bottom arc a contraction, and a top arc
the insertion of `∑ₘ eₘ ⊗ e*ₘ`.

**Formalization Note** Top row = output (row index), bottom row = input (column index). The
identification `V ≃ V*` "on restriction to `O_n`" of p. 9 is `e_i ↔ e*_i`, which is why the same
formula serves the last `s` positions. -/
def diagOp (n : ℕ) {r s : ℕ} (D : WalledDiagram r s) : Op n (r + s) :=
  Matrix.of fun i j => if ∀ x, Sum.elim i j x = Sum.elim i j (D.1 x) then 1 else 0

end DotySW.Deranged


