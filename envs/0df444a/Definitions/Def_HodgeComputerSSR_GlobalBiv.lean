-- Prove2me | Definitions.Def_HodgeComputerSSR_GlobalBiv
-- name    : HodgeComputerSSR_GlobalBiv
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T21:55:40.186795+00:00
-- url     : https://prove2.me/theorems/90723aed-ced3-45b0-9e0f-35582a35808a
-- title:
--   Sparse bivariate encoding `LHS_glob_biv` of the global residue cancellation identity
-- statement:
--   Pure bivariate leaf defining `L5_glob_e` and `LHS_glob_biv` encoding $L_5^2 (P_{\mathrm{horiz},\mathrm{biv}} + 105 R_{U,\mathrm{biv}}) + 5 R_{\infty,\mathrm{biv}} + 147 R_{Q5,\mathrm{biv}}$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5.lean#L244-L251

import Definitions.Def_HodgeComputerSSR_BivReduce
import Definitions.Def_HodgeComputerSSR_RUData
import Definitions.Def_HodgeComputerSSR_RInfData
import Definitions.Def_HodgeComputerSSR_RQ5Data

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.VerticalData SymmetricSexticResidual.VerticalIdentity
  SymmetricSexticResidual.LocalResidueData
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

def L5_glob_e : Expr :=
  .add (.add (.mul (.num 77) (.var 0)) (.mul (.num (-210)) (.var 1))) (.num 45)

def LHS_glob_biv : Biv :=
  VerticalIdentity.bivAdd (scale (.pow L5_glob_e 2) 0 0 (VerticalIdentity.bivAdd P_horiz_biv (scale (.num 105) 0 0 RU_biv)))
    (VerticalIdentity.bivAdd (scale (.num 5) 0 0 RInf_biv) (scale (.num 147) 0 0 RQ5_biv))


end SymmetricSexticResidual.LocalResidueQ5


