-- Prove2me | Definitions.Def_DotySW_Deranged_coord
-- name    : DotySW_Deranged_coord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:57.101142+00:00
-- url     : https://prove2.me/theorems/82421fed-feec-4ecd-94ee-bc17f1b5d561
-- title:
--   The coefficient of a diagram in an element of $\mathcal B^{(n)}_{r,s}$
-- statement:
--   For $x\in\mathcal B^{(n)}_{r,s}$ and an $(r,s)$-diagram $D$, this is the coefficient of $D$ when $x$ is written in the basis of diagrams.
--
--   **Formalization Note** The published algebra consists of matrices on the diagrams. Left multiplication by a diagram $A$ sends the identity diagram to $A$ with no loops, so the coefficient of $D$ in $x$ is the matrix entry of $x$ at row $D$, column the identity diagram.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.1, unnumbered, p. 7

import Mathlib
import Definitions.Def_DotySW_Deranged_WB

namespace DotySW.Deranged

open WalledBrauer.Blocks

/-- **The coefficient of a diagram in an element of `B^{(n)}_{r,s}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.1, unnumbered, p. 7.

`coord x D` is the coefficient of the diagram `D` in `x`.

**Formalization Note** `WalledBrauerAlgebra` is realised by left multiplications on the free module
on the diagrams, and `leftMul A` sends the identity diagram to `A` with no loops. So the
coefficient of `D` in `x` is the entry of the matrix of `x` at row `D`, column the identity diagram
(the column of the identity diagram is `x` applied to the unit). -/
noncomputable def coord {n r s : ℕ} (x : WB n r s) (D : WalledDiagram r s) : ℂ :=
  (show ↥(walledBrauerSubalgebra ℂ r s (n : ℂ)) from x).1 D (WalledDiagram.one r s)

end DotySW.Deranged


