-- Prove2me | Definitions.Def_HodgeComputerSSR_Q5K5Geom
-- name    : HodgeComputerSSR_Q5K5Geom
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T22:02:07.964798+00:00
-- url     : https://prove2.me/theorems/aca4d68a-4376-423f-8eba-275dfdc852aa
-- title:
--   $K_5$ instances `acK`, `gsqK`, `gtK` and shifted trace polynomials `R13_int_p`, `R12_int_p`
-- statement:
--   Instantiates `k5Ops`, `evalUPolyK5`, `evalBivLK5`, `acK`, `gsqK`, `gtK`, and the polynomial combinations `A0U_U_p..Bv_1701_p`, `R13_int_p`, and `R12_int_p` in $K_5$ without importing `Q5Weights` or `CoverParams`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Poly.lean#L22-L128

import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_BivEval
import Definitions.Def_HodgeComputerSSR_Q5Geom
import Mathlib.Algebra.Polynomial.Div

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.LocalResidueU0
  PolynomialEncoding.KroneckerCheck Polynomial
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

abbrev k5Ops : PolyOps K5 := ringOps K5
abbrev v3P3_SQ : ℕ → P3Z := v3P3_01
abbrev v3P3_SQT : ℕ → P3Z := v3P3_012

def v3K5 : Fin 3 → K5
  | 0 => S_K
  | 1 => Q_K
  | 2 => T_K

def evalP3K5 : P3Z →+* K5 :=
  MvPolynomial.eval₂Hom (Int.castRingHom K5) v3K5

lemma poly3ToK5Rel : PolyOpsRel poly3Ops k5Ops (fun p x => evalP3K5 p = x) :=
  poly3ToRingRel v3K5

def vK5_SQ : ℕ → K5
  | 0 => S_K
  | 1 => Q_K
  | _ => 0

def evalSQ_K5 (e : Expr) : K5 := ringEval vK5_SQ e

lemma evalP3K5_ringEval_SQ (e : Expr) :
    evalP3K5 (ringEval v3P3_SQ e) = evalSQ_K5 e := by
  induction e with
  | num c => simp [evalP3K5, evalSQ_K5, ringEval]
  | natCast n => simp [evalP3K5, evalSQ_K5, ringEval]
  | intCast z => simp [evalP3K5, evalSQ_K5, ringEval]
  | var j =>
    match j with
    | 0 => simp [evalP3K5, evalSQ_K5, ringEval, v3P3_SQ, v3P3_01, v3K5, vK5_SQ]
    | 1 => simp [evalP3K5, evalSQ_K5, ringEval, v3P3_SQ, v3P3_01, v3K5, vK5_SQ]
    | _ + 2 => simp [evalP3K5, evalSQ_K5, ringEval, v3P3_SQ, v3P3_01, vK5_SQ]
  | neg a ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]
  | add a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
  | sub a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
  | mul a b ha hb => simp [evalSQ_K5, ringEval] at ha hb ⊢; rw [ha, hb]
  | pow a k ha => simp [evalSQ_K5, ringEval] at ha ⊢; rw [ha]

-- Nonvanishing of `fac_0 .. fac_6` and `D_all_expr` in `K5` via `evLoc` mod 1009!

abbrev evalUPolyK5 : UPoly K5 → K5[X] := evalUPoly
abbrev evalYListK5 : UPoly K5 → K5 := evalYList y_K
abbrev evalBivLK5 : BivL K5 → K5 := evalBivL x_K y_K
abbrev evalUBivLK5 : UBivL K5 → K5[X] := evalUBivL x_K y_K

lemma evalUPolyK5_uAdd (a b : UPoly K5) :
    evalUPolyK5 (uAdd k5Ops a b) = evalUPolyK5 a + evalUPolyK5 b := evalUPoly_uAdd a b
lemma evalUPolyK5_uNeg (a : UPoly K5) :
    evalUPolyK5 (uNeg k5Ops a) = -evalUPolyK5 a := evalUPoly_uNeg a
lemma evalUPolyK5_uSub (a b : UPoly K5) :
    evalUPolyK5 (uSub k5Ops a b) = evalUPolyK5 a - evalUPolyK5 b := evalUPoly_uSub a b
lemma evalUPolyK5_uSc (c : K5) (a : UPoly K5) :
    evalUPolyK5 (uSc k5Ops c a) = Polynomial.C c * evalUPolyK5 a := evalUPoly_uSc c a
lemma evalUPolyK5_uShift (a : UPoly K5) :
    evalUPolyK5 (uShift k5Ops a) = Polynomial.X * evalUPolyK5 a := evalUPoly_uShift a
lemma evalUPolyK5_uMul (a b : UPoly K5) :
    evalUPolyK5 (uMul k5Ops a b) = evalUPolyK5 a * evalUPolyK5 b := evalUPoly_uMul a b
lemma evalUPolyK5_uTail (a : UPoly K5) :
    evalUPolyK5 a = Polynomial.C (a.headD 0) + Polynomial.X * evalUPolyK5 (uTail a) := evalUPoly_uTail a
lemma evalUPolyK5_coeff (a : UPoly K5) (k : ℕ) :
    (evalUPolyK5 a).coeff k = a.getD k 0 := evalUPoly_coeff a k
lemma evalUPolyK5_natDegree_le (a : UPoly K5) (k : ℕ) (hk : a.length ≤ k) :
    (evalUPolyK5 a).coeff k = 0 := evalUPoly_coeff_eq_zero_of_le a hk
lemma evalBivLK5_bivAdd (a b : BivL K5) :
    evalBivLK5 (bivAdd k5Ops a b) = evalBivLK5 a + evalBivLK5 b := evalBivL_bivAdd x_K y_K a b
lemma evalBivLK5_bivNeg (a : BivL K5) :
    evalBivLK5 (bivNeg k5Ops a) = -evalBivLK5 a := evalBivL_bivNeg x_K y_K a
lemma evalBivLK5_bivSub (a b : BivL K5) :
    evalBivLK5 (bivSub k5Ops a b) = evalBivLK5 a - evalBivLK5 b := evalBivL_bivSub x_K y_K a b
lemma evalBivLK5_bivSc (c : K5) (a : BivL K5) :
    evalBivLK5 (bivSc k5Ops c a) = c * evalBivLK5 a := evalBivL_bivSc x_K y_K c a
lemma evalBivLK5_bivMul (a b : BivL K5) :
    evalBivLK5 (bivMul k5Ops a b) = evalBivLK5 a * evalBivLK5 b := evalBivL_bivMul x_K y_K a b
lemma evalUBivLK5_ubAdd (a b : UBivL K5) :
    evalUBivLK5 (ubAdd k5Ops a b) = evalUBivLK5 a + evalUBivLK5 b := evalUBivL_ubAdd x_K y_K a b
lemma evalUBivLK5_ubNeg (a : UBivL K5) :
    evalUBivLK5 (ubNeg k5Ops a) = -evalUBivLK5 a := evalUBivL_ubNeg x_K y_K a
lemma evalUBivLK5_ubSub (a b : UBivL K5) :
    evalUBivLK5 (ubSub k5Ops a b) = evalUBivLK5 a - evalUBivLK5 b := evalUBivL_ubSub x_K y_K a b
lemma evalUBivLK5_ubSc (c : K5) (a : UBivL K5) :
    evalUBivLK5 (ubSc k5Ops c a) = Polynomial.C c * evalUBivLK5 a := evalUBivL_ubSc x_K y_K c a
lemma evalUBivLK5_ubBmul (b : BivL K5) (a : UBivL K5) :
    evalUBivLK5 (ubBmul k5Ops b a) = Polynomial.C (evalBivLK5 b) * evalUBivLK5 a := evalUBivL_ubBmul x_K y_K b a
lemma evalUBivLK5_ubShift (a : UBivL K5) :
    evalUBivLK5 (ubShift a) = Polynomial.X * evalUBivLK5 a := evalUBivL_ubShift x_K y_K a
lemma evalUBivLK5_ubMulU (u : UPoly K5) (a : UBivL K5) :
    evalUBivLK5 (ubMulU k5Ops u a) = evalUPolyK5 u * evalUBivLK5 a := evalUBivL_ubMulU x_K y_K u a
lemma evalUBivLK5_ubSynDiv1Rem (a : UBivL K5) :
    evalUBivLK5 a = Polynomial.C (evalBivLK5 (ubSynDiv1Rem k5Ops a).1) +
      (Polynomial.X - 1) * evalUBivLK5 (ubSynDiv1Rem k5Ops a).2 := evalUBivL_ubSynDiv1Rem x_K y_K a
lemma evalUBivLK5_coeff (a : UBivL K5) (k : ℕ) :
    (evalUBivLK5 a).coeff k = evalBivLK5 (a.getD k []) := evalUBivL_coeff x_K y_K a k
lemma evalBivLK5_combineBivDot_uAdd (B : UBivL K5) (c1 c2 : UPoly K5) :
    evalBivLK5 (combineBivDot k5Ops B (uAdd k5Ops c1 c2)) =
      evalBivLK5 (combineBivDot k5Ops B c1) + evalBivLK5 (combineBivDot k5Ops B c2) :=
  evalBivL_combineBivDot_uAdd x_K y_K B c1 c2
lemma evalBivLK5_combineBivDot_uSc (s : K5) (B : UBivL K5) (c : UPoly K5) :
    evalBivLK5 (combineBivDot k5Ops B (uSc k5Ops s c)) =
      s * evalBivLK5 (combineBivDot k5Ops B c) :=
  evalBivL_combineBivDot_uSc x_K y_K s B c


lemma evalBivLK5_bivRedOnce_H0 (b : BivL K5) :
    evalBivLK5 (bivRedOnce k5Ops (21 * S_K) (-(21 * T_K)) (-(7 * H0_K)) b) =
      (21 * S_K) * evalBivLK5 b := by
  have hx2 : 21 * S_K * x_K ^ 2 = -(21 * T_K) * y_K ^ 2 + -(7 * H0_K) := by
    have hF := x_K_sq_relation
    change 3 * S_K * x_K ^ 2 + 3 * T_K * y_K ^ 2 + H0_K = 0 at hF
    linear_combination 7 * hF
  exact evalBivL_bivRedOnce hx2 b

lemma evalBivLK5_combineBivDot_dotW (A : UPoly K5) (B : UBivL K5) (W : UPoly K5) (shift : ℕ)
    (hBlen : B.length ≤ 5) (hdeg : A.length + B.length + shift ≤ 15) :
    evalBivLK5 (combineBivDot k5Ops B (dotW k5Ops A W shift)) =
      ∑ k : Fin 13, ((Polynomial.X ^ shift * evalUPolyK5 A * evalUBivLK5 B).coeff (k.val + 1)) * W.getD k.val 0 :=
  evalBivL_combineBivDot_dotW x_K y_K 13 5 A B W shift hBlen hdeg

abbrev uEval_uAdd_P3Z := @uEval_uAdd P3Z _
abbrev uEval_uNeg_P3Z := @uEval_uNeg P3Z _
abbrev uEval_uSub_P3Z := @uEval_uSub P3Z _
abbrev uEval_uSc_P3Z := @uEval_uSc P3Z _
abbrev uEval_uShift_P3Z := @uEval_uShift P3Z _
abbrev uEval_uMul_P3Z := @uEval_uMul P3Z _
abbrev uEval_uMonomial_P3Z := @uEval_uMonomial P3Z _
abbrev uEval_uPow_P3Z := @uEval_uPow P3Z _

lemma evalP3K5_ringEval_SQT (e : Expr) :
    evalP3K5 (ringEval v3P3_SQT e) = ringEval vK5 e := by
  induction e with
  | num c => simp [evalP3K5, ringEval]
  | natCast n => simp [evalP3K5, ringEval]
  | intCast z => simp [evalP3K5, ringEval]
  | var j =>
      match j with
      | 0 => simp [evalP3K5, ringEval, v3P3_SQT, v3P3_012, v3K5, vK5]
      | 1 => simp [evalP3K5, ringEval, v3P3_SQT, v3P3_012, v3K5, vK5]
      | 2 => simp [evalP3K5, ringEval, v3P3_SQT, v3P3_012, v3K5, vK5]
      | _ + 3 => simp [evalP3K5, ringEval, v3P3_SQT, v3P3_012, vK5]
  | neg a ha => simp [ringEval] at ha ⊢; rw [ha]
  | add a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
  | sub a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
  | mul a b ha hb => simp [ringEval] at ha hb ⊢; rw [ha, hb]
  | pow a k ha => simp [ringEval] at ha ⊢; rw [ha]

-- Shift-invariant `numM_lead3` and degree-3 expansion of `numM` along `(a1 * z, b1 * z + b0)`

def acK : ACache K5 := evalACache k5Ops S_K Q_K
def gsqK : GeomSQ K5 := evalGeomSQ k5Ops S_K Q_K
def gtK : GeomT K5 := evalGeomT k5Ops S_K acK.ca_p acK.cb_p gsqK T_K

def A0U_U_p : K5[X] :=
  evalUPolyK5 (uTail acK.A0U_t0) + Polynomial.C T_K * evalUPolyK5 (uTail acK.A0U_t1)

def A0V_p : K5[X] :=
  evalUPolyK5 acK.A0V_t0 + Polynomial.C T_K * evalUPolyK5 acK.A0V_t1 +
    Polynomial.C (T_K ^ 2) * evalUPolyK5 acK.A0V_t2

def AY2_p : K5[X] :=
  evalUPolyK5 acK.AY2_t0 + Polynomial.C T_K * evalUPolyK5 acK.AY2_t1

def AY3_p : K5[X] :=
  evalUPolyK5 acK.AY3_t0 + Polynomial.C T_K * evalUPolyK5 acK.AY3_t1

def AX2_p : K5[X] :=
  evalUPolyK5 acK.AX2_t0 + Polynomial.C T_K * evalUPolyK5 acK.AX2_t1 +
    Polynomial.C (T_K ^ 2) * evalUPolyK5 acK.AX2_t2

def Bv_1701_p : K5[X] :=
  evalUPolyK5 acK.Bv_SQ + Polynomial.C gtK.Bv1_T_1701 * Polynomial.X


def R13_int_p : K5[X] :=
  Polynomial.C (7 * gtK.Cv0_243) * (Polynomial.X * A0U_U_p * (evalUBivLK5 gtK.q1_0_div_sc - evalUBivLK5 gtK.q1_2_div_sc)) +
  Polynomial.C (45927 * gtK.Cv0_243 * gtK.H0_7_2) * (Polynomial.X * AY3_p * evalUBivLK5 gtK.DY2_qE_63) +
  Polynomial.C 7 * (A0V_p * evalUBivLK5 gtK.q1_1_sc) +
  Polynomial.C (243 * gtK.H0_7_2) * (AY2_p * evalUBivLK5 gtK.qY_0_321489 + AX2_p * evalUBivLK5 gtK.qX_0_sc) -
  A0V_p * Bv_1701_p * evalUBivLK5 gtK.q1_0_div_sc

def R12_int_p : K5[X] := R13_int_p.divX


end SymmetricSexticResidual.LocalResidueQ5


