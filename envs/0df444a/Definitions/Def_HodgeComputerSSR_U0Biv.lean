-- Prove2me | Definitions.Def_HodgeComputerSSR_U0Biv
-- name    : HodgeComputerSSR_U0Biv
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T10:11:10.911324+00:00
-- url     : https://prove2.me/theorems/ce4566fc-f43e-4737-917f-662c8b2a35fb
-- title:
--   Sparse bivariate encoding of the $U = 0$ Branch-2 residue identity
-- statement:
--   Defines the sparse bivariate polynomial ASTs `LHS_U0_biv` and `RHS_U0_biv` encoding the cleared $U = 0$ Branch-2 residue comparison against `RU_biv`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L2251-L2650

import Definitions.Def_HodgeComputerSSR_BivReduce
import Definitions.Def_HodgeComputerSSR_RUData

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.LocalResidueData
  SymmetricSexticResidual.VerticalIdentity
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

def eA5 : Expr := .sub (.mul (.num 5) eS) (.mul (.num 9) eQ)
def e5S3Q : Expr := .sub (.mul (.num 5) eS) (.mul (.num 3) eQ)
def eB5 : Expr := .sub eT (.num 3)

def dH0_7_e : Fin 3 → Expr
  | 0 => .add (.add (.mul (.num (-42)) (.pow eS 2)) (.mul (.num 84) (.mul eS eQ)))
           (.mul (.num (-21)) (.pow eQ 2))
  | 1 => .add (.add (.mul (.num 42) (.pow eS 2)) (.mul (.num (-42)) (.mul eS eQ)))
           (.add (.mul (.num (-42)) (.pow eQ 2)) (.add (.mul (.num 10) eQ) (.num 10)))
  | 2 => .add (.add (.mul (.num (-42)) (.pow eT 2)) (.mul (.num 84) eT)) (.num (-21))

def dF5_7_biv : Fin 5 → Biv
  | 0 => .cons (.num 21) 2 0 (.cons (dH0_7_e 0) 0 0 .nil)
  | 1 => .cons (dH0_7_e 1) 0 0 .nil
  | 2 => .cons (.num 21) 0 2 (.cons (dH0_7_e 2) 0 0 .nil)
  | 3 => .cons (.mul (.num 42) eS) 1 0 .nil
  | 4 => .cons (.mul (.num 42) eT) 0 1 .nil

def dDX2_biv : Fin 5 → Biv
  | 0 => .cons (.num (-27)) 2 0
      (.cons (.add (.mul (.num 100) eS) (.mul (.num (-90)) eQ)) 1 0
        (.cons (.add (.add (.mul (.num (-69)) (.pow eS 2)) (.mul (.num 164) (.mul eS eQ)))
          (.mul (.num (-71)) (.pow eQ 2))) 0 0 .nil))
  | 1 => .cons (.mul (.num (-90)) eS) 1 0
      (.cons (.add (.add (.mul (.num 82) (.pow eS 2)) (.mul (.num (-142)) (.mul eS eQ)))
        (.mul (.num (-12)) (.pow eQ 2))) 0 0 .nil)
  | 2 => .nil
  | 3 => .cons (.mul (.num (-54)) eS) 1 0
      (.cons (.add (.mul (.num 50) (.pow eS 2)) (.mul (.num (-90)) (.mul eS eQ))) 0 0 .nil)
  | 4 => .nil

-- `243 * br_V0` (coeff of `V^1` at `U = 0` of `243 * br_fn k`):
def LY_V1_27_biv : Biv :=
  .cons (.num 27) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 45)) 0 0 .nil)

def LY_V1_9_biv : Biv :=
  .cons (.num 9) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 15)) 0 0 .nil)

def br_V0_243_biv : Fin 5 → Biv
  | 0 => scale (.mul (.num (-5)) (.mul eT e5S3Q)) 0 0 LY_V1_27_biv
  | 1 => scale (.mul (.num 30) (.mul eS eT)) 0 0 LY_V1_27_biv
  | 2 => scale (.mul (.num 5) (.mul eS eA5)) 0 0 LY_V1_9_biv
  | 3 => .nil
  | 4 => .cons (.mul (.num 90) (.mul (.mul eS eT) eA5)) 0 0 .nil

-- `81 * om_V0` (coeff of `V^1` at `U = 0` of `81 * om_fn p q`):
-- `omX(0) = [25*S - 15*Q, -30*S, 0, 0, 0]`, `omY_V1 = [0, 0, -25*T + 9*y + 15, 0, 18*T]`!
def omX0_e : Fin 5 → Expr
  | 0 => .sub (.mul (.num 25) eS) (.mul (.num 15) eQ)
  | 1 => .mul (.num (-30)) eS
  | _ => .num 0

def omY_V1_biv : Fin 5 → Biv
  | 2 => .cons (.num 9) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 15)) 0 0 .nil)
  | 4 => .cons (.mul (.num 18) eT) 0 0 .nil
  | _ => .nil

def om_V0_81_biv (p q : Fin 5) : Biv :=
  bivSub (scale (omX0_e p) 0 0 (omY_V1_biv q)) (scale (omX0_e q) 0 0 (omY_V1_biv p))

-- `1701 * QY_V0 i` (`= 243 * 7 * QY_V0 i` so both `3 * (81 * om)` and `243 * br` share factor `243`!)
def F_contract_7_biv (f2 : Fin 5 → Fin 5 → Biv) (i : Fin 3) : Biv :=
  let idx : Fin 5 := match i with | 0 => 0 | 1 => 1 | 2 => 2
  bivAdd (bivAdd (bivMul (dF5_7_biv 4) (f2 idx 3)) (bivMul (dF5_7_biv 3) (f2 4 idx)))
    (bivMul (dF5_7_biv idx) (f2 3 4))

def QY_V0_1701_biv (i : Fin 3) : Biv :=
  let Om := F_contract_7_biv (fun p q => scale (.mul (.num 3) (.mul eS eT)) 0 0 (om_V0_81_biv p q)) i
  let dX := F_contract_7_biv (fun p q => scale (.mul eS eT) 0 0
    (bivSub (bivMul (dDX2_biv p) (br_V0_243_biv q)) (bivMul (dDX2_biv q) (br_V0_243_biv p)))) i
  bivMul DY2_biv (bivSub (bivMul DX2_biv Om) dX)

-- `9 * EB_V0 / (S * A5) = -40 * S * T * x * W2`:
def EB_V0_9_div_SA5_biv : Biv :=
  scale (.mul (.num (-40)) (.mul eS eT)) 1 0 W2_biv

-- Build `q1_int_v_divSA52` and `q1_int_e_red_divSA52` directly as `Biv`s!
-- Wait: recall `QY_V0_1701_biv = 1701 * QY_V0 = 3 * 567 * QY_V0`!
-- So `3 * q1_int = 3 * 11907 * q1`:
--   Term 1 (`H0 * A1 * qY`): `(7 * H0) * (25) * (QY_V0_1701 · (a_num, b_num, den_ab))` (div by `S * A5^2`!)
--     Check factor: `7 * 27 * (1701 / 9) = 7 * 27 * 189 = 35721 = 3 * 11907`!
--   Term 2 (`cA1_div_v * EB`): `189 * (cA1_21_div_A5) * (EB_V0_9_div_SA5)` (div by `S * A5^2`!)
--     Check factor: `189 * 21 * 9 = 35721 = 3 * 11907`!!
def cA1_21_div_A5_e : Fin 3 → Expr
  | 0 => .sub (.mul H0_int_e (.mul (.num 25) (.sub (.mul (.num 15) eS) (.mul (.num 9) eQ))))
           (.mul (.mul (.num 25) (.mul eS eA5)) (dH0_7_e 0))
  | 1 => .sub (.mul H0_int_e (.mul (.num (-450)) eS))
           (.mul (.mul (.num 25) (.mul eS eA5)) (dH0_7_e 1))
  | 2 => .neg (.mul (.mul (.num 25) (.mul eS eA5)) (dH0_7_e 2))

def q1_v_35721_biv : Biv :=
  let a0_e := .mul (.num 6) (.pow eS 2)
  let b0_e := .mul (.num 6) (.mul eS eQ)
  let d0_e := .mul (.num 6) (.mul eS eB5)
  let qY0 := bivAdd (bivAdd (scale a0_e 0 0 (QY_V0_1701_biv 0)) (scale b0_e 0 0 (QY_V0_1701_biv 1)))
    (scale d0_e 0 0 (QY_V0_1701_biv 2))
  let t1 := scale (.mul (.num 25) H0_int_e) 0 0 qY0
  let cA0_e := .add (.add (.mul (cA1_21_div_A5_e 0) a0_e) (.mul (cA1_21_div_A5_e 1) b0_e))
    (.mul (cA1_21_div_A5_e 2) d0_e)
  let t2 := scale (.mul (.num 189) cA0_e) 0 0 EB_V0_9_div_SA5_biv
  bivAdd t1 t2

def q1_e_35721_divB5_biv : Biv :=
  let a1_e := .mul (.num 6) eS
  let b1_e := e5S3Q
  let qY1 := bivAdd (scale a1_e 0 0 (QY_V0_1701_biv 0)) (scale b1_e 0 0 (QY_V0_1701_biv 1))
  let t1 := scale (.mul (.num 25) H0_int_e) 0 0 qY1
  let cA1_e := .add (.mul (cA1_21_div_A5_e 0) a1_e) (.mul (cA1_21_div_A5_e 1) b1_e)
  let t2 := scale (.mul (.num 189) cA1_e) 0 0 EB_V0_9_div_SA5_biv
  bivAdd t1 t2

def Q_quad_U0_e : Expr :=
  .add (.add (.add (.mul (.num 11943020) (.pow eS 2)) (.mul (.num (-876486)) (.mul eS eQ)))
    (.add (.mul (.num 8382500) (.mul eS eT)) (.mul (.num 5029500) (.mul eQ eT))))
  (.add (.mul (.num (-14837025)) eS) (.mul (.num (-33647355)) eQ))

def L_U0_e : Expr :=
  .add (.add (.mul (.num 225) eS) (.mul (.num (-45)) eQ)) (.add (.mul (.num 77) eT) (.num (-210)))

def LHS_U0_biv : Biv :=
  let t1 := scale (.mul (.num 173215980) (.mul eS e5S3Q)) 0 0 q1_e_35721_divB5_biv
  let t2 := scale (.mul (.num (-42)) Q_quad_U0_e) 0 0 q1_v_35721_biv
  let t3 := scale (.mul (.num 8248380) (.mul e5S3Q L_U0_e)) 0 0 q1_v_35721_biv
  bivReduceX2 (bivAdd (bivAdd t1 t2) t3)

def RHS_U0_biv : Biv :=
  -- `21 * 3 * 189000 = 11907000` (extra factor 3 because `q1_35721 = 3 * q1_11907`)!
  scale (.mul (.num 11907000) (.mul (.pow eS 3) eA5)) 0 0 RU_biv

-- THE KERNEL-VERIFIED 5-VARIABLE `U = 0` RESIDUE IDENTITY (< 1s!)

end SymmetricSexticResidual.LocalResidueU0


