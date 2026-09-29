-- Prove2me | Definitions.Def_HighDimStat_RandomMatrices_LoewnerLE
-- name    : HighDimStat_RandomMatrices_LoewnerLE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:18:39.168272+00:00
-- url     : https://prove2.me/theorems/003e222e-ac9a-4682-b49a-1872dcc2b972
-- title:
--   The Loewner (positive semidefinite) order on symmetric matrices
-- statement:
--   The **Loewner order** $A \preceq B$ on symmetric matrices: $A \preceq B$ iff $B-A$ is positive
--   semidefinite. Used throughout Section 6.4.1 to state every matrix tail condition (Eqs.
--   (6.27)-(6.31)), including Definition 6.10's Bernstein condition for matrices.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 168 (PDF p. 188), Section 6.4.1

import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **Loewner (positive semidefinite) order** `A ⪯ B` on symmetric matrices, used throughout
Wainwright, *High-Dimensional Statistics* (2019), Section 6.4.1, to state matrix tail conditions
(Eqs. (6.27)-(6.31)): `A ⪯ B` iff `B - A` is positive semidefinite. -/
def LoewnerLE {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (B - A).PosSemidef

end HighDimStat.RandomMatrices


