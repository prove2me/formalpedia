-- Prove2me | Definitions.Def_HodgeComputerSSR_LocalInfBivId
-- name    : HodgeComputerSSR_LocalInfBivId
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T17:41:33.788399+00:00
-- url     : https://prove2.me/theorems/bc73303b-c46e-4b63-a28e-d8490f664405
-- title:
--   Sparse bivariate comparison ASTs `LHS_Uinf_biv` and `RHS_Uinf_biv` for $U = \infty$
-- statement:
--   Defines `LHS_Uinf_biv` and `RHS_Uinf_biv` comparing the assembled Branch-1 $t^1$-coefficient at $U = \infty$ against `-RInf_biv`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L1494-L1511

import Definitions.Def_HodgeComputerSSR_LocalInfBiv
import Definitions.Def_HodgeComputerSSR_RInfData

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.LocalResidueData
  SymmetricSexticResidual.VerticalIdentity SymmetricSexticResidual.LocalResidueU0
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

def LHS_Uinf_raw_biv : Biv :=
  let s1 := bscE (.mul (.mul (.num 539715645) L5_e) S3Q_e) q1_0_u1_biv
  let s2 := bscE (.mul (.mul (.num 6174) L5_e) M01_q_e) q1_m1_u1_biv
  let s3 := bscE (.mul (.mul (.mul (.mul (.num 3593175390) L5_e) w0_sc4_e) S3Q_e) (.pow H0_int_e 2)) cQX_0_biv
  let s4 := bscE (.mul (.mul (.num (-3671535)) P44_e) S3Q_e) q1_m1_u1_biv
  let s5 := bscE (.mul (.mul (.mul (.num 8566915) (.pow L5_e 2)) lin_A3_e) S3Q_e) q1_m1_u0_biv
  let s6 := bscE (.mul (.mul (.mul (.num 63) (.pow L5_e 2)) lin_A3_e) A32_2_q_e) q1_m1_u1_biv
  let s7 := bscE (.mul (.mul (.num 49) (.pow L5_e 2)) A32_2_q_e) q1_m1_u0_biv
  let s8 := bscE (.mul (.mul (.num 147) (.pow L5_e 2)) A32_1_q_e) q1_m1_u1_biv
  bivAdd (bivAdd (bivAdd s1 s2) (bivAdd s3 s4)) (bivAdd (bivAdd s5 s6) (bivAdd s7 s8))

def LHS_Uinf_biv : Biv := bivReduceX2 (bivReduceX2 LHS_Uinf_raw_biv)

def RHS_Uinf_biv : Biv :=
  bscE (.mul (.pow (.mul (.num 21) eS) 2)
    (.mul (.mul (.mul (.num (-40500)) S3Q_e) (.pow eT 2)) (.pow T59_e 3))) RInf_biv


end SymmetricSexticResidual.LocalResidueInf


