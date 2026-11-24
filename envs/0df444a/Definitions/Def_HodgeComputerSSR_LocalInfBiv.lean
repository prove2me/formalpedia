-- Prove2me | Definitions.Def_HodgeComputerSSR_LocalInfBiv
-- name    : HodgeComputerSSR_LocalInfBiv
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T17:28:14.063612+00:00
-- url     : https://prove2.me/theorems/a0906114-b806-44e7-b8ed-bac70f6b5a0c
-- title:
--   Sparse bivariate encodings for $U = \infty$ branch-1 numerators and jets
-- statement:
--   Defines the sparse bivariate polynomial ASTs `P44_e`, `M01_q_e`, `QY*_biv`, `QX*_biv`, `EB*_biv`, `q1_*_biv`, and `evalBivK5_bscE` without importing cover algebra or `RInfData`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L1291-L1515

import Definitions.Def_HodgeComputerSSR_BivReduce

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.VerticalData
  SymmetricSexticResidual.VerticalIdentity SymmetricSexticResidual.LocalResidueU0
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

def P44_e : Expr :=
  .add (.add (.add (.add (.add (.num 20510415) (.mul (.num (-45278190)) eT)) (.add (.mul (.num (-135184545)) (.pow eT 2)) (.add (.mul (.num (-13243230)) (.pow eT 3)) (.mul (.num (-496300770)) eQ)))) (.add (.add (.mul (.mul (.num 1002263220) eQ) eT) (.add (.mul (.mul (.num 1619567460) eQ) (.pow eT 2)) (.mul (.mul (.num 61801740) eQ) (.pow eT 3)))) (.add (.mul (.num 1510998300) (.pow eQ 2)) (.add (.mul (.mul (.num (-9227925000)) (.pow eQ 2)) eT) (.mul (.mul (.num (-4613962500)) (.pow eQ 2)) (.pow eT 2)))))) (.add (.add (.add (.mul (.num 4883417910) (.pow eQ 3)) (.mul (.mul (.num 25838190000) (.pow eQ 3)) eT)) (.add (.mul (.num (-20513855880)) (.pow eQ 4)) (.add (.mul (.num 141076404) eS) (.mul (.mul (.num (-302433264)) eS) eT)))) (.add (.add (.mul (.mul (.num (-657628902)) eS) (.pow eT 2)) (.add (.mul (.mul (.num (-22660638)) eS) (.pow eT 3)) (.mul (.mul (.num (-1013761980)) eS) eQ))) (.add (.mul (.mul (.mul (.num 6278958000) eS) eQ) eT) (.add (.mul (.mul (.mul (.num 3978922500) eS) eQ) (.pow eT 2)) (.mul (.mul (.num (-4586695470)) eS) (.pow eQ 2))))))) (.add (.add (.add (.add (.mul (.mul (.mul (.num (-28116396000)) eS) (.pow eQ 2)) eT) (.mul (.mul (.mul (.num (-1389150000)) eS) (.pow eQ 2)) (.pow eT 2))) (.add (.mul (.mul (.num 28084223286) eS) (.pow eQ 3)) (.add (.mul (.mul (.mul (.num 2593080000) eS) (.pow eQ 3)) eT) (.mul (.num 161280315) (.pow eS 2))))) (.add (.add (.mul (.mul (.num (-1055687850)) (.pow eS 2)) eT) (.add (.mul (.mul (.num (-843577875)) (.pow eS 2)) (.pow eT 2)) (.mul (.mul (.num 1449439110) (.pow eS 2)) eQ))) (.add (.mul (.mul (.mul (.num 10141721100) (.pow eS 2)) eQ) eT) (.add (.mul (.mul (.mul (.num 1065015000) (.pow eS 2)) eQ) (.pow eT 2)) (.mul (.mul (.num (-14449808646)) (.pow eS 2)) (.pow eQ 2)))))) (.add (.add (.add (.mul (.mul (.mul (.num (-2722734000)) (.pow eS 2)) (.pow eQ 2)) eT) (.mul (.mul (.mul (.num (-108045000)) (.pow eS 2)) (.pow eQ 2)) (.pow eT 2))) (.add (.mul (.num (-155306970)) (.pow eS 3)) (.add (.mul (.mul (.num (-1212264900)) (.pow eS 3)) eT) (.mul (.mul (.num (-203742000)) (.pow eS 3)) (.pow eT 2))))) (.add (.add (.mul (.mul (.num 3313480842) (.pow eS 3)) eQ) (.add (.mul (.mul (.mul (.num 950796000) (.pow eS 3)) eQ) eT) (.mul (.mul (.mul (.num 79233000) (.pow eS 3)) eQ) (.pow eT 2)))) (.add (.mul (.num (-285894273)) (.pow eS 4)) (.add (.mul (.mul (.num (-110397980)) (.pow eS 4)) eT) (.mul (.mul (.num (-14526050)) (.pow eS 4)) (.pow eT 2)))))))

def M01_q_e : Expr :=
  .add (.add (.add (.add (.mul (.num (-2238759810)) eQ) (.add (.mul (.mul (.num 5237503740) eQ) eT) (.mul (.mul (.num (-3040030980)) eQ) (.pow eT 2)))) (.add (.mul (.mul (.num 525029505) eQ) (.pow eT 3)) (.add (.mul (.num 7683624765) (.pow eQ 2)) (.mul (.mul (.num (-372008700)) (.pow eQ 2)) eT)))) (.add (.add (.mul (.num 10237067550) (.pow eQ 3)) (.add (.mul (.mul (.num 1928934000) (.pow eQ 3)) eT) (.mul (.num 4197469815) (.pow eQ 4)))) (.add (.add (.mul (.num 746253270) eS) (.mul (.mul (.num (-1745834580)) eS) eT)) (.add (.mul (.mul (.num 1013343660) eS) (.pow eT 2)) (.mul (.mul (.num (-175009835)) eS) (.pow eT 3)))))) (.add (.add (.add (.mul (.mul (.num (-4575240450)) eS) eQ) (.add (.mul (.mul (.mul (.num 275562000) eS) eQ) eT) (.mul (.mul (.num (-8309917980)) eS) (.pow eQ 2)))) (.add (.add (.mul (.mul (.mul (.num (-2057529600)) eS) (.pow eQ 2)) eT) (.mul (.mul (.num (-7561149120)) eS) (.pow eQ 3))) (.add (.mul (.num 671344065) (.pow eS 2)) (.mul (.mul (.num (-50519700)) (.pow eS 2)) eT)))) (.add (.add (.mul (.mul (.num 2244102813) (.pow eS 2)) eQ) (.add (.mul (.mul (.mul (.num 730851660) (.pow eS 2)) eQ) eT) (.mul (.mul (.num 4310935335) (.pow eS 2)) (.pow eQ 2)))) (.add (.add (.mul (.num (-203860701)) (.pow eS 3)) (.mul (.mul (.num (-86444820)) (.pow eS 3)) eT)) (.add (.mul (.mul (.num (-968078160)) (.pow eS 3)) eQ) (.mul (.num 71921850) (.pow eS 4))))))

def A32_2_q_e : Expr :=
  .add (.add (.add (.mul (.num 3000564) eQ) (.mul (.mul (.num 78318540) eQ) eT)) (.add (.mul (.num (-197659350)) (.pow eQ 2)) (.mul (.num (-1000188)) eS))) (.add (.add (.mul (.mul (.num (-26106180)) eS) eT) (.mul (.mul (.num 124429830) eS) eQ)) (.add (.mul (.mul (.mul (.num 18357675) eS) eQ) eT) (.add (.mul (.num (-19514460)) (.pow eS 2)) (.mul (.mul (.num (-6119225)) (.pow eS 2)) eT))))

def A32_1_q_e : Expr :=
  .add (.add (.add (.add (.mul (.num 482717070) eQ) (.mul (.mul (.num (-275562000)) eQ) eT)) (.add (.mul (.mul (.num (-1157172750)) eQ) (.pow eT 2)) (.add (.mul (.num 1567877310) (.pow eQ 2)) (.mul (.mul (.num (-1841555250)) (.pow eQ 2)) eT)))) (.add (.add (.mul (.num (-160905690)) eS) (.add (.mul (.mul (.num 91854000) eS) eT) (.mul (.mul (.num 385724250) eS) (.pow eT 2)))) (.add (.mul (.mul (.num (-1036249848)) eS) eQ) (.add (.mul (.mul (.mul (.num 1656892800) eS) eQ) eT) (.mul (.mul (.mul (.num (-783185400)) eS) eQ) (.pow eT 2)))))) (.add (.add (.add (.mul (.mul (.num (-1185956100)) eS) (.pow eQ 2)) (.mul (.mul (.mul (.num 1976593500) eS) (.pow eQ 2)) eT)) (.add (.mul (.num 171208026) (.pow eS 2)) (.add (.mul (.mul (.num (-347680350)) (.pow eS 2)) eT) (.mul (.mul (.num 261061800) (.pow eS 2)) (.pow eT 2))))) (.add (.add (.mul (.mul (.num 779622795) (.pow eS 2)) eQ) (.add (.mul (.mul (.mul (.num (-1244298300)) (.pow eS 2)) eQ) eT) (.mul (.mul (.mul (.num (-91788375)) (.pow eS 2)) eQ) (.pow eT 2)))) (.add (.mul (.num (-128101365)) (.pow eS 3)) (.add (.mul (.mul (.num 195144600) (.pow eS 3)) eT) (.mul (.mul (.num 30596125) (.pow eS 3)) (.pow eT 2))))))


def L5_e : Expr := .add (.sub (.mul (.num 77) eS) (.mul (.num 210) eQ)) (.num 45)
def S3Q_e : Expr := .sub eS (.mul (.num 3) eQ)
def T59_e : Expr := .sub (.mul (.num 5) eT) (.num 9)
def T53_e : Expr := .sub (.mul (.num 5) eT) (.num 3)
def A5_e : Expr := .sub (.mul (.num 5) eS) (.mul (.num 9) eQ)
def c0_num_e : Expr := .neg (.mul S3Q_e T53_e)
def w0_sc4_e : Expr := .mul (.mul (.num (-25)) eT) (.pow T59_e 2)
def Bv1_1701_e : Expr :=
  .add (.add (.mul (.num 7)
    (.add (.sub (.add (.sub (.add (.sub (.add (.mul (.num 143) (.pow eS 3)) (.mul (.num (-828)) (.mul (.pow eS 2) eQ)))
      (.mul (.num (-1404)) (.mul eS (.pow eQ 2)))) (.mul (.num 594) (.pow eQ 3)))
      (.mul (.num 143) (.pow eT 3))) (.mul (.num 828) (.pow eT 2)))
      (.mul (.num 1404) eT)) (.num (-594))))
    (.mul (.num 1215) (.pow eQ 2))) (.mul (.num 2430) eQ)

-- Clean Bv1_1701_e matching `verify_uinf_biv_exact.py` verbatim!
def Bv1_1701_exact_e : Expr :=
  .add (.add (.mul (.num 7)
    (.sub (.add (.sub (.add (.sub (.add (.sub (.mul (.num 143) (.pow eS 3))
      (.mul (.num 828) (.mul (.pow eS 2) eQ))) (.mul (.num 1404) (.mul eS (.pow eQ 2))))
      (.mul (.num 594) (.pow eQ 3))) (.mul (.num 143) (.pow eT 3)))
      (.mul (.num 828) (.pow eT 2))) (.mul (.num 1404) eT)) (.num 594)))
    (.mul (.num 1215) (.pow eQ 2))) (.mul (.num 2430) eQ)

def rb_num_28_e : Expr :=
  .mul (.num (-3)) (.add (.add (.add (.sub (.mul (.num 119) (.pow eS 2))
    (.mul (.num 560) (.mul eS eQ))) (.mul (.num 630) (.pow eQ 2))) (.mul (.num 90) eQ)) (.num 90))
def rb_sc_28_e : Expr := .mul S3Q_e rb_num_28_e

def dH0_7_inf_e : Fin 3 → Expr
  | 0 => .sub (.add (.mul (.num (-42)) (.pow eS 2)) (.mul (.num 84) (.mul eS eQ))) (.mul (.num 21) (.pow eQ 2))
  | 1 => .add (.add (.sub (.sub (.mul (.num 42) (.pow eS 2)) (.mul (.num 42) (.mul eS eQ)))
           (.mul (.num 42) (.pow eQ 2))) (.mul (.num 10) eQ)) (.num 10)
  | 2 => .sub (.add (.mul (.num (-42)) (.pow eT 2)) (.mul (.num 84) eT)) (.num 21)

def dH0_301_21_e : Expr := .add (.mul (.num 3) (dH0_7_inf_e 0)) (dH0_7_inf_e 1)

def bscE (e : Expr) (p : Biv) : Biv := scale e 0 0 p

def dF5_7_inf_biv : Fin 5 → Biv
  | 0 => .cons (.num 21) 2 0 (.cons (dH0_7_inf_e 0) 0 0 .nil)
  | 1 => .cons (dH0_7_inf_e 1) 0 0 .nil
  | 2 => .cons (.num 21) 0 2 (.cons (dH0_7_inf_e 2) 0 0 .nil)
  | 3 => .cons (.mul (.num 42) eS) 1 0 .nil
  | 4 => .cons (.mul (.num 42) eT) 0 1 .nil

def dDX2_inf_biv : Fin 5 → Biv
  | 0 => .cons (.num (-27)) 2 0 (.cons (.sub (.mul (.num 100) eS) (.mul (.num 90) eQ)) 1 0
          (.cons (.add (.sub (.mul (.num (-69)) (.pow eS 2)) (.mul (.num (-164)) (.mul eS eQ))) (.mul (.num (-71)) (.pow eQ 2))) 0 0 .nil))
  | 1 => .cons (.mul (.num (-90)) eS) 1 0
          (.cons (.add (.sub (.mul (.num 82) (.pow eS 2)) (.mul (.num 142) (.mul eS eQ))) (.mul (.num (-12)) (.pow eQ 2))) 0 0 .nil)
  | 3 => .cons (.mul (.num (-54)) eS) 1 0 (.cons (.sub (.mul (.num 50) (.pow eS 2)) (.mul (.num 90) (.mul eS eQ))) 0 0 .nil)
  | _ => .nil

def dDY2_inf_biv : Fin 5 → Biv
  | 2 => .cons (.num (-27)) 0 2 (.cons (.sub (.mul (.num 100) eT) (.num 90)) 0 1
          (.cons (.add (.sub (.mul (.num (-69)) (.pow eT 2)) (.mul (.num (-164)) eT)) (.num (-71))) 0 0 .nil))
  | 4 => .cons (.mul (.num (-54)) eT) 0 1 (.cons (.sub (.mul (.num 50) (.pow eT 2)) (.mul (.num 90) eT)) 0 0 .nil)
  | _ => .nil

def LX1_9_biv : Biv := .cons (.num 9) 1 0 (.cons (.add (.mul (.num (-25)) eS) (.mul (.num 15) eQ)) 0 0 .nil)
def LX1_27_biv : Biv := .cons (.num 27) 1 0 (.cons (.add (.mul (.num (-25)) eS) (.mul (.num 45) eQ)) 0 0 .nil)
def LY1_9_biv : Biv := .cons (.num 9) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 15)) 0 0 .nil)
def LY1_27_biv : Biv := .cons (.num 27) 0 1 (.cons (.add (.mul (.num (-25)) eT) (.num 45)) 0 0 .nil)

def br_10_243_biv : Fin 5 → Biv
  | 0 => bscE (.mul (.mul (.num (-5)) eT) T59_e) LX1_9_biv
  | 1 => .cons (.mul (.mul (.mul (.num (-150)) eT) T59_e) eS) 0 0 .nil
  | 2 => bscE (.mul (.mul (.num 5) T53_e) eS) LX1_27_biv
  | 3 => .cons (.mul (.mul (.mul (.num (-90)) eT) T59_e) eS) 0 0 .nil
  | 4 => .nil

def br_00_243_biv : Fin 5 → Biv
  | 0 => .cons (.mul (.mul (.mul (.num 25) eT) T59_e) (.add (.mul (.num (-5)) eS) (.mul (.num 3) eQ))) 0 0 .nil
  | 1 => .cons (.mul (.mul (.mul (.num 150) eT) T59_e) eS) 0 0 .nil
  | 2 => .cons (.mul (.mul (.mul (.num (-25)) T53_e) (.add (.mul (.num (-5)) eS) (.mul (.num 9) eQ))) eS) 0 0 .nil
  | _ => .nil

def br_11_243_biv : Fin 5 → Biv
  | 0 => bscE (.neg eT) (bivMul LY1_27_biv LX1_9_biv)
  | 1 => bscE (.mul (.mul (.num (-30)) eT) eS) LY1_27_biv
  | 2 => bscE eS (bivMul LY1_9_biv LX1_27_biv)
  | 3 => bscE (.mul (.mul (.num (-18)) eT) eS) LY1_27_biv
  | 4 => bscE (.mul (.mul (.num 18) eT) eS) LX1_27_biv

def om_10_raw (p q : Fin 5) : Biv := match p, q with
  | 0, 2 => bscE (.mul (.num 5) T53_e) LX1_9_biv
  | 1, 2 => .cons (.mul (.mul (.num 150) T53_e) eS) 0 0 .nil
  | 2, 3 => .cons (.mul (.mul (.num (-90)) T53_e) eS) 0 0 .nil
  | _, _ => .nil

def om_10_81_biv (p q : Fin 5) : Biv := bivSub (om_10_raw p q) (om_10_raw q p)

def om_00_raw (p q : Fin 5) : Biv := match p, q with
  | 0, 2 => .cons (.mul (.mul (.num (-25)) T53_e) (.add (.mul (.num (-5)) eS) (.mul (.num 3) eQ))) 0 0 .nil
  | 1, 2 => .cons (.mul (.mul (.num (-150)) T53_e) eS) 0 0 .nil
  | _, _ => .nil

def om_00_81_biv (p q : Fin 5) : Biv := bivSub (om_00_raw p q) (om_00_raw q p)

def om_11_raw (p q : Fin 5) : Biv := match p, q with
  | 0, 2 => bivMul LY1_9_biv LX1_9_biv
  | 0, 4 => bscE (.mul (.num 18) eT) LX1_9_biv
  | 1, 2 => bscE (.mul (.num 30) eS) LY1_9_biv
  | 1, 4 => .cons (.mul (.mul (.num 540) eT) eS) 0 0 .nil
  | 2, 3 => bscE (.mul (.num (-18)) eS) LY1_9_biv
  | 3, 4 => .cons (.mul (.mul (.num 324) eT) eS) 0 0 .nil
  | _, _ => .nil

def om_11_81_biv (p q : Fin 5) : Biv := bivSub (om_11_raw p q) (om_11_raw q p)

def F_c_inf_biv (f2 : Fin 5 → Fin 5 → Biv) (i : Fin 3) : Biv :=
  let idx : Fin 5 := match i with | 0 => 0 | 1 => 1 | 2 => 2
  bivAdd (bivAdd (bivMul (dF5_7_inf_biv 4) (f2 idx 3))
    (bivMul (dF5_7_inf_biv 3) (f2 4 idx))) (bivMul (dF5_7_inf_biv idx) (f2 3 4))

def make_QY_biv (br243 : Fin 5 → Biv) (om81 : Fin 5 → Fin 5 → Biv) (i : Fin 3) : Biv :=
  let Om := F_c_inf_biv (fun a b => bscE (.mul eS eT) (om81 a b)) i
  let dX := F_c_inf_biv (fun a b => bscE (.mul eS eT)
    (bivSub (bivMul (dDX2_inf_biv a) (br243 b)) (bivMul (dDX2_inf_biv b) (br243 a)))) i
  bivMul DY2_biv (bivSub (bivScale 3 (bivMul DX2_biv Om)) dX)

def make_QX_biv (br243 : Fin 5 → Biv) (om81 : Fin 5 → Fin 5 → Biv) (i : Fin 3) : Biv :=
  let Om := F_c_inf_biv (fun a b => bscE (.mul eS eT) (om81 a b)) i
  let dY := F_c_inf_biv (fun a b => bscE (.mul eS eT)
    (bivSub (bivMul (dDY2_inf_biv a) (br243 b)) (bivMul (dDY2_inf_biv b) (br243 a)))) i
  bivMul DX2_biv (bivAdd (bivScale (-3) (bivMul DY2_biv Om)) dY)

def QX10_biv (i : Fin 3) : Biv := make_QX_biv br_10_243_biv om_10_81_biv i
def QY10_biv (i : Fin 3) : Biv := make_QY_biv br_10_243_biv om_10_81_biv i
def QX00_biv (i : Fin 3) : Biv := make_QX_biv br_00_243_biv om_00_81_biv i
def QY00_biv (i : Fin 3) : Biv := make_QY_biv br_00_243_biv om_00_81_biv i
def QX11_biv (i : Fin 3) : Biv := make_QX_biv br_11_243_biv om_11_81_biv i
def QY11_biv (i : Fin 3) : Biv := make_QY_biv br_11_243_biv om_11_81_biv i

def EB10_biv : Biv :=
  bivScale 12 (bivMul W2_biv (bivSub (scale eT 0 1 (br_10_243_biv 3))
    (scale eS 1 0 (br_10_243_biv 4))))

def EB11_biv : Biv :=
  bivScale 12 (bivMul W2_biv (bivSub (scale eT 0 1 (br_11_243_biv 3))
    (scale eS 1 0 (br_11_243_biv 4))))

def cQX_0_biv : Biv := bivAdd (bivScale 3 (QX10_biv 0)) (QX10_biv 1)
def cQX_00_biv : Biv := bivAdd (bivScale 3 (QX00_biv 0)) (QX00_biv 1)
def cQX_11_biv : Biv := bivAdd (bivScale 3 (QX11_biv 0)) (QX11_biv 1)
def cQY_00_biv : Biv := bivAdd (bivScale 3 (QY00_biv 0)) (QY00_biv 1)
def cQY_11_biv : Biv := bivAdd (bivScale 3 (QY11_biv 0)) (QY11_biv 1)

def q1_m1_u1_biv : Biv :=
  bscE (.mul (.mul (.num 25) eT) (.pow T59_e 2))
    (bivAdd (bscE H0_int_e cQX_0_biv) (bscE (.mul (.num 7) dH0_301_21_e) EB10_biv))

def q1_m1_u0_biv : Biv :=
  let t1 := bscE (.mul (.mul (.mul (.num (-75)) eT) (.pow T59_e 2)) H0_int_e)
    (bivAdd (bscE c0_num_e (QY10_biv 1)) (bscE (.mul (.mul (.num 3) eT) T59_e) (QY10_biv 2)))
  let t2 := bscE (.mul (.mul (.mul (.num 75) eT) (.pow T59_e 2)) H0_int_e)
    (bivAdd (bscE c0_num_e (QX10_biv 1)) (bscE (.mul (.mul (.num 3) eT) T59_e) (QX10_biv 2)))
  let t3 := bscE (.mul (.num (-525))
    (.sub (.mul (.mul (.mul (.mul (.num 9) eT) (.pow T59_e 2)) T53_e) H0_int_e)
      (.mul (.mul eT (.pow T59_e 2)) (.add (.mul (dH0_7_inf_e 1) c0_num_e)
        (.mul (.mul (.mul (.num 3) eT) T59_e) (dH0_7_inf_e 2)))))) EB10_biv
  bivAdd (bivAdd t1 t2) t3

def cQX_1_biv : Biv :=
  bivAdd (bivAdd (bscE (.neg Bv1_1701_exact_e) cQX_0_biv) (bscE rb_sc_28_e (QX10_biv 1)))
    (bivAdd (bscE (.mul (.num 28) (.pow S3Q_e 3)) cQX_00_biv) (bscE (.mul (.num 7) w0_sc4_e) cQX_11_biv))

def q1_0_u1_biv : Biv :=
  let qa := bscE (.mul (.mul (.mul (.num (-25)) eT) (.pow T59_e 2)) H0_int_e)
    (bivAdd (bscE rb_sc_28_e (QY10_biv 1))
      (bivAdd (bscE (.mul (.num 28) (.pow S3Q_e 3)) cQY_00_biv) (bscE (.mul (.num 7) w0_sc4_e) cQY_11_biv)))
  let qb := bivSub
    (bscE (.mul (.mul (.mul (.num 25) eT) (.pow T59_e 2)) H0_int_e)
      (bivAdd cQX_1_biv (bscE (.mul (.num 28) (.pow S3Q_e 3)) cQX_0_biv)))
    (bscE (.mul (.mul (.mul (.num 28) (.pow (.sub eT (.num 3)) 3)) w0_sc4_e) H0_int_e) cQX_0_biv)
  let qc1_fac : Expr :=
    .sub (.sub (.mul (.mul H0_int_e w0_sc4_e)
      (.add (.mul (.num 63) rb_num_28_e) (.mul (.mul (.num 33075) A5_e) (.sub eS eQ))))
      (.mul (.mul (.mul (.mul (.num 1225) eS) (.pow A5_e 2)) w0_sc4_e) dH0_301_21_e))
      (.mul (.mul (.mul (.mul (.num 175) eT) (.pow T59_e 2)) rb_sc_28_e) (dH0_7_inf_e 1))
  let qc := bivAdd (bscE (.neg qc1_fac) EB10_biv)
    (bscE (.mul (.mul (.mul (.mul (.num 1225) w0_sc4_e) eT) (.pow T59_e 2)) dH0_301_21_e)
      (bivAdd EB11_biv EB10_biv))
  bivAdd (bivAdd qa qb) qc

def lin_A3_e : Expr :=
  .sub (.add (.sub (.add (.mul (.num 35) (.mul eS eT)) (.mul (.num 133) eS)) (.mul (.num 420) eQ))
    (.mul (.num 225) eT)) (.num 45)


lemma evalBivK5_bscE (e : Expr) (p : Biv) :
    evalBivK5 (bscE e p) = ringEval vK5 e * evalBivK5 p := by
  simpa only [bscE, pow_zero, mul_one] using evalBivK5_scale e 0 0 p


end SymmetricSexticResidual.LocalResidueInf


