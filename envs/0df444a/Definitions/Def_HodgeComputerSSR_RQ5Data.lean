-- Prove2me | Definitions.Def_HodgeComputerSSR_RQ5Data
-- name    : HodgeComputerSSR_RQ5Data
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T10:08:52.340856+00:00
-- url     : https://prove2.me/theorems/d8313b8c-9741-4ca9-b410-0deb71f9b967
-- title:
--   $K_5$ evaluation `toK5_RQ5` of the $Q_5(U) = 0$ residue sum
-- statement:
--   Lifts `RQ5_biv` and `D_RQ5` to `toK5_RQ5` in $K_5$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueData.lean

import Definitions.Def_HodgeComputerSSR_BivEval
import Definitions.Def_HodgeComputerSSR_RQ5Biv

set_option autoImplicit false

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.LocalResidueData
def toK5_RQ5 : K5 := evalBivK5 RQ5_biv / (D_RQ5 : K5)
end SymmetricSexticResidual.LocalResidueU0


