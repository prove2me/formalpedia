-- Prove2me | Definitions.Def_DepthOneQExp_hOp
-- name    : DepthOneQExp_hOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:32.187192+00:00
-- url     : https://prove2.me/theorems/bf83d91b-56ab-4a69-87dc-3086260c4bbc
-- title:
--   The operator $H = X_1\otimes X_1 + Z_1\otimes Z_1$
-- statement:
--   On two copies of an $n$-qubit register,
--   $$
--   H = X_1\otimes X_1 + Z_1\otimes Z_1 ,
--   $$
--   where $X_1 = X\otimes I_{2^{n-1}}$ and $Z_1 = Z\otimes I_{2^{n-1}}$ act on qubit 1 of each copy (Eqs. (2.45), (2.47)). It is twice the average of the two added gates $P_{m+1}\otimes P_{m+1}$, $P_{m+2}\otimes P_{m+2}$ of Theorem 2.13.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eqs. (2.45) and (2.47), pp.13–14

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_permToMatrix
import Definitions.Def_DepthOneQExp_xPerm
import Definitions.Def_DepthOneQExp_zMat

namespace DepthOneQExp

open scoped Kronecker

/-- The operator `H = X_1 ⊗ X_1 + Z_1 ⊗ Z_1` on two copies of an `n`-qubit register
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eqs. (2.45) and (2.47),
pp.13–14), where `X_1 = X ⊗ I_{2^{n−1}}` and `Z_1 = Z ⊗ I_{2^{n−1}}` act on qubit 1 (0-based index
`0`). -/
noncomputable def hOp (n : ℕ) :
    Matrix (MITMSynthesis.Q n × MITMSynthesis.Q n) (MITMSynthesis.Q n × MITMSynthesis.Q n) ℂ :=
  permToMatrix (xPerm n 0) ⊗ₖ permToMatrix (xPerm n 0) + zMat n 0 ⊗ₖ zMat n 0

end DepthOneQExp


