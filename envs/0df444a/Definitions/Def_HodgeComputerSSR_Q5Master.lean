-- Prove2me | Definitions.Def_HodgeComputerSSR_Q5Master
-- name    : HodgeComputerSSR_Q5Master
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T22:02:43.984347+00:00
-- url     : https://prove2.me/theorems/c9f26aa7-3d3c-476e-a1f1-229f04517e74
-- title:
--   Master factored cache `SQCache`, `evalBTot`, `evalTStep`, and 2D Kronecker checkers
-- statement:
--   Pure leaf defining `SQCache`, `evalSQCache`, `evalBTot`, `evalTStep`, `SQCacheRel`, and the 2D Kronecker $(2^{474}, 2^{70 \cdot 474})$ × $T$-grid checkers `checkMasterBounds` and `checkMasterTChunk`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Poly.lean#L501-L770

import Definitions.Def_HodgeComputerSSR_Q5Geom
import Definitions.Def_HodgeComputerSSR_Q5Weights
import Definitions.Def_HodgeComputerSSR_RQ5Biv

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.Q5WeightsData SymmetricSexticResidual.LocalResidueData
  PolynomialEncoding.KroneckerCheck
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len

structure SQCache (α : Type*) where
  W : UPoly α
  D_div_L2 : α
  ac : ACache α
  gsq : GeomSQ α
  d_A0U_t0 : UPoly α
  d_A0U_t1 : UPoly α
  d_A0V_t0 : UPoly α
  d_A0V_t1 : UPoly α
  d_A0V_t2 : UPoly α
  d_A0V_U_t0 : UPoly α
  d_A0V_U_t1 : UPoly α
  d_A0V_U_t2 : UPoly α
  d_A0VBv_t0 : UPoly α
  d_A0VBv_t1 : UPoly α
  d_A0VBv_t2 : UPoly α
  d_AY2_t0 : UPoly α
  d_AY2_t1 : UPoly α
  d_AY3_t0 : UPoly α
  d_AY3_t1 : UPoly α
  d_AX2_t0 : UPoly α
  d_AX2_t1 : UPoly α
  d_AX2_t2 : UPoly α
  RQ5_T : List (List (UPoly α))

def evalSQCache {α : Type*} (o : PolyOps α) (S Q : α) : SQCache α :=
  letB (powList o S 30 (o.ofInt 1)) fun pS =>
  letB (powList o Q 37 (o.ofInt 1)) fun pQ =>
  letB (o.add (o.mul (o.ofInt (-5)) S) (o.mul (o.ofInt 9) Q)) fun f2 =>
  letB (o.add (o.neg S) (o.mul (o.ofInt 3) Q)) fun f3 =>
  letB (o.add (o.add (o.ofInt (-45)) (o.mul (o.ofInt (-77)) S)) (o.mul (o.ofInt 210) Q)) fun f4 =>
  letB (o.mul f2 f2) fun f2_2 =>
  letB (o.mul f2_2 f2_2) fun f2_4 =>
  letB (o.mul f2_4 f2_2) fun f2_6 =>
  letB (o.mul f2_6 f2) fun f2_7 =>
  letB (o.mul (o.mul f3 f3) f3) fun f3_3 =>
  letB (o.mul f3_3 f3_3) fun f3_6 =>
  letB (o.mul f3_6 f3_3) fun f3_9 =>
  letB (o.mul f3_9 f3_3) fun f3_12 =>
  letB (o.mul f3_12 f3) fun f3_13 =>
  letB (o.mul f4 f4) fun f4_2 =>
  letB (o.mul f3_13 f4_2) fun d0 =>
  letB (o.mul (o.mul (o.mul S f2_2) f3_13) f4_2) fun d1 =>
  letB (o.mul (o.mul (o.mul S f2_4) f3_13) f4_2) fun d2 =>
  letB (o.mul (o.mul (o.mul S f2_6) f3_13) f4_2) fun d3 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_13) f4_2) fun d4 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_12) f4_2) fun d8 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_9) f4_2) fun d9 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_6) f4_2) fun d10 =>
  letB (o.mul (o.mul (o.mul S f2_7) f3_3) f4) fun d11 =>
  letB (o.mul S f2_7) fun d12 =>
  letB ([o.mul (o.ofInt (N_k_mul 0)) (o.mul d0 (evalExpr2 o S Q pS pQ (N_k_expr 0))),
         o.mul (o.ofInt (N_k_mul 1)) (o.mul d1 (evalExpr2 o S Q pS pQ (N_k_expr 1))),
         o.mul (o.ofInt (N_k_mul 2)) (o.mul d2 (evalExpr2 o S Q pS pQ (N_k_expr 2))),
         o.mul (o.ofInt (N_k_mul 3)) (o.mul d3 (evalExpr2 o S Q pS pQ (N_k_expr 3))),
         o.mul (o.ofInt (N_k_mul 4)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 4))),
         o.mul (o.ofInt (N_k_mul 5)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 5))),
         o.mul (o.ofInt (N_k_mul 6)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 6))),
         o.mul (o.ofInt (N_k_mul 7)) (o.mul d4 (evalExpr2 o S Q pS pQ (N_k_expr 7))),
         o.mul (o.ofInt (N_k_mul 8)) (o.mul d8 (evalExpr2 o S Q pS pQ (N_k_expr 8))),
         o.mul (o.ofInt (N_k_mul 9)) (o.mul d9 (evalExpr2 o S Q pS pQ (N_k_expr 9))),
         o.mul (o.ofInt (N_k_mul 10)) (o.mul d10 (evalExpr2 o S Q pS pQ (N_k_expr 10))),
         o.mul (o.ofInt (N_k_mul 11)) (o.mul d11 (evalExpr2 o S Q pS pQ (N_k_expr 11))),
         o.mul (o.ofInt (N_k_mul 12)) (o.mul d12 (evalExpr2 o S Q pS pQ (N_k_expr 12)))] : UPoly α) fun W =>
  letB (o.mul (o.mul (o.mul (o.mul (o.mul Q S) f2_7) f3_13) (o.pow (evalExpr2 o S Q pS pQ fac_5) 4))
      (evalExpr2 o S Q pS pQ fac_6)) fun D_div_L2 =>
  letB (evalACache o S Q) fun ac =>
  letB (evalGeomSQ o S Q) fun gsq =>
  ⟨W, D_div_L2, ac, gsq,
   dotW o (uTail ac.A0U_t0) W 1, dotW o (uTail ac.A0U_t1) W 1,
   dotW o ac.A0V_t0 W 0, dotW o ac.A0V_t1 W 0, dotW o ac.A0V_t2 W 0,
   dotW o ac.A0V_t0 W 1, dotW o ac.A0V_t1 W 1, dotW o ac.A0V_t2 W 1,
   dotW o (uMul o ac.A0V_t0 ac.Bv_SQ) W 0, dotW o (uMul o ac.A0V_t1 ac.Bv_SQ) W 0, dotW o (uMul o ac.A0V_t2 ac.Bv_SQ) W 0,
   dotW o ac.AY2_t0 W 0, dotW o ac.AY2_t1 W 0,
   dotW o ac.AY3_t0 W 1, dotW o ac.AY3_t1 W 1,
   dotW o ac.AX2_t0 W 0, dotW o ac.AX2_t1 W 0, dotW o ac.AX2_t2 W 0,
   [[evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y0, evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y1,
     evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y2, evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y3,
     evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y4, evalExpr3PolyT o S Q pS pQ RQ5_biv_x0y5],
    [evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y0, evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y1,
     evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y2, evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y3,
     evalExpr3PolyT o S Q pS pQ RQ5_biv_x1y4]]⟩


def evalBTot {α : Type*} (o : PolyOps α) (cache : SQCache α) (gt : GeomT α) (T : α) : BivL α :=
  letB (o.mul T T) fun T2 =>
  letB (uAdd o cache.d_A0U_t0 (uSc o T cache.d_A0U_t1)) fun d_A0U =>
  letB (uAdd o (uAdd o cache.d_A0V_t0 (uSc o T cache.d_A0V_t1)) (uSc o T2 cache.d_A0V_t2)) fun d_A0V =>
  letB (uAdd o (uAdd o cache.d_A0V_U_t0 (uSc o T cache.d_A0V_U_t1)) (uSc o T2 cache.d_A0V_U_t2)) fun d_A0V_U =>
  letB (uAdd o (uAdd o (uAdd o cache.d_A0VBv_t0 (uSc o T cache.d_A0VBv_t1)) (uSc o T2 cache.d_A0VBv_t2))
      (uSc o gt.Bv1_T_1701 d_A0V_U)) fun d_A0VBv =>
  letB (uAdd o cache.d_AY2_t0 (uSc o T cache.d_AY2_t1)) fun d_AY2 =>
  letB (uAdd o cache.d_AY3_t0 (uSc o T cache.d_AY3_t1)) fun d_AY3 =>
  letB (uAdd o (uAdd o cache.d_AX2_t0 (uSc o T cache.d_AX2_t1)) (uSc o T2 cache.d_AX2_t2)) fun d_AX2 =>
  bivAdd o (bivAdd o (bivAdd o
      (combineBivDot o (ubSub o gt.q1_0_div_sc gt.q1_2_div_sc) (uSc o (o.mul (o.ofInt 7) gt.Cv0_243) d_A0U))
      (combineBivDot o gt.DY2_qE_63 (uSc o (o.mul (o.ofInt 45927) (o.mul gt.Cv0_243 gt.H0_7_2)) d_AY3)))
      (combineBivDot o gt.q1_1_sc (uSc o (o.ofInt 7) d_A0V)))
    (bivAdd o (bivSc o (o.mul (o.ofInt 243) gt.H0_7_2)
      (bivAdd o (combineBivDot o gt.qY_0_321489 d_AY2) (combineBivDot o gt.qX_0_sc d_AX2)))
      (bivNeg o (combineBivDot o gt.q1_0_div_sc d_A0VBv)))

def evalTStep {α : Type*} (o : PolyOps α) (S : α) (cache : SQCache α) (T : α) : BivL α :=
  letB (evalGeomT o S cache.ac.ca_p cache.ac.cb_p cache.gsq T) fun gt =>
  letB (evalBTot o cache gt T) fun B_tot =>
  letB (o.mul (o.ofInt 21) S) fun s21 =>
  letB (o.neg (o.mul (o.ofInt 21) T)) fun t21 =>
  letB (o.neg gt.H0_7) fun nh0 =>
  letB (bivRedOnce o s21 t21 nh0 (bivRedOnce o s21 t21 nh0 B_tot)) fun lhs =>
  letB (o.mul (o.ofInt C_RHS_int) (o.mul (o.mul s21 s21) (o.mul gt.Cv0_int cache.D_div_L2))) fun rhs_sc =>
  letB (cache.RQ5_T.map (fun row => row.map (fun p => uEval o p T))) fun rhs_raw =>
  bivSub o lhs (bivSc o rhs_sc rhs_raw)

-- `PolyOpsRel` preservation for `evalACache`, `evalGeomSQ`, `evalSQCache`, `evalGeomT`, `evalBTot`, `evalTStep`

section SQRelDef
variable {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
structure SQCacheRel (R : α → β → Prop) (a : SQCache α) (b : SQCache β) : Prop where
  W : URel R a.W b.W
  D_div_L2 : R a.D_div_L2 b.D_div_L2
  ac : ACacheRel R a.ac b.ac
  gsq : GeomSQRel R a.gsq b.gsq
  d_A0U_t0 : URel R a.d_A0U_t0 b.d_A0U_t0
  d_A0U_t1 : URel R a.d_A0U_t1 b.d_A0U_t1
  d_A0V_t0 : URel R a.d_A0V_t0 b.d_A0V_t0
  d_A0V_t1 : URel R a.d_A0V_t1 b.d_A0V_t1
  d_A0V_t2 : URel R a.d_A0V_t2 b.d_A0V_t2
  d_A0V_U_t0 : URel R a.d_A0V_U_t0 b.d_A0V_U_t0
  d_A0V_U_t1 : URel R a.d_A0V_U_t1 b.d_A0V_U_t1
  d_A0V_U_t2 : URel R a.d_A0V_U_t2 b.d_A0V_U_t2
  d_A0VBv_t0 : URel R a.d_A0VBv_t0 b.d_A0VBv_t0
  d_A0VBv_t1 : URel R a.d_A0VBv_t1 b.d_A0VBv_t1
  d_A0VBv_t2 : URel R a.d_A0VBv_t2 b.d_A0VBv_t2
  d_AY2_t0 : URel R a.d_AY2_t0 b.d_AY2_t0
  d_AY2_t1 : URel R a.d_AY2_t1 b.d_AY2_t1
  d_AY3_t0 : URel R a.d_AY3_t0 b.d_AY3_t0
  d_AY3_t1 : URel R a.d_AY3_t1 b.d_AY3_t1
  d_AX2_t0 : URel R a.d_AX2_t0 b.d_AX2_t0
  d_AX2_t1 : URel R a.d_AX2_t1 b.d_AX2_t1
  d_AX2_t2 : URel R a.d_AX2_t2 b.d_AX2_t2
  RQ5_T : List.Forall₂ (List.Forall₂ (URel R)) a.RQ5_T b.RQ5_T

end SQRelDef

def masterBits : ℕ := 474
def masterDegS : ℕ := 70
def masterLim : ℕ := Nat.pow 2 masterBits
def bS2D : ℤ := Int.ofNat masterLim
def bQ2D : ℤ := Int.ofNat (Nat.pow 2 (masterDegS * masterBits))
def c2D : SQCache ℤ := evalSQCache intOps bS2D bQ2D
def cPB2D : SQCache PB := evalSQCache pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 1⟩

def checkMasterBounds : Bool :=
  (evalTStep pbOps ⟨1, 0, 0, 1⟩ cPB2D ⟨0, 0, 1, 10⟩).all fun row =>
    row.all fun b => Nat.blt b.dS masterDegS && Nat.blt b.dT 20 && Nat.blt b.M masterLim

def checkMasterTChunk (lo : ℤ) (n : ℕ) : Bool :=
  allRange lo n fun t =>
    (evalTStep intOps bS2D c2D t).all fun row =>
      row.all fun z => z == 0

lemma checkMasterTChunk_append (lo : ℤ) (m n : ℕ) :
    checkMasterTChunk lo (m + n) = (checkMasterTChunk lo m && checkMasterTChunk (lo + (m : ℤ)) n) :=
  allRange_append lo m n _


end SymmetricSexticResidual.LocalResidueQ5


