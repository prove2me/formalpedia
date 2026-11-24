-- Prove2me | Definitions.Def_HodgeComputerSSR_Q5Geom
-- name    : HodgeComputerSSR_Q5Geom
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T21:54:52.912351+00:00
-- url     : https://prove2.me/theorems/add0c098-e018-4d4e-9485-33a97f8fed54
-- title:
--   Polymorphic factored geometry caches (`ACache`, `GeomSQ`, `GeomT`) and relational specs
-- statement:
--   Pure leaf importing only `PolyOps`, defining the polymorphic factored evaluation caches `ACache`, `GeomSQ`, `GeomT`, their `PolyOpsRel` predicates `ACacheRel`, `GeomSQRel`, `GeomTRel`, and unit-length trackers `acUnit`, `gsqUnit`, `gtUnit`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Poly.lean#L311-L788

import Definitions.Def_HodgeComputerFormal_PolyOps

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace SymmetricSexticResidual.LocalResidueQ5
open PolynomialEncoding.KroneckerCheck
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len

abbrev uOps : PolyOps Unit := unitOps

abbrev dotW {α : Type*} (o : PolyOps α) (A W : UPoly α) (shift : ℕ) : UPoly α :=
  PolynomialEncoding.PolyOps.dotW o 13 5 A W shift

lemma dotW_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {A1 A2 W1 W2} (hA : URel R A1 A2) (hW : URel R W1 W2) (shift : ℕ) :
    URel R (dotW o1 A1 W1 shift) (dotW o2 A2 W2 shift) :=
  PolynomialEncoding.PolyOps.dotW_rel hR hA hW 13 5 shift

lemma dotW_len {α : Type*} (o : PolyOps α) (A W : UPoly α) (sh : ℕ) :
    (dotW o A W sh).length = 5 :=
  PolynomialEncoding.PolyOps.dotW_len o 13 5 A W sh


def L_all_A : ℤ := 235267436250
def M_A_int : ℤ := L_all_A * 16 * 45927 * 567 ^ 4
def M_mid_int : ℤ := 2250423
def M_R_int : ℤ := M_A_int * 1701 * M_mid_int
def C_RHS_int : ℤ := -5438812994401448072650932000000000000000

structure ACache (α : Type*) where
  ca_p : UPoly α
  cb_p : UPoly α
  A0U_t0 : UPoly α
  A0U_t1 : UPoly α
  A0V_t0 : UPoly α
  A0V_t1 : UPoly α
  A0V_t2 : UPoly α
  AY2_t0 : UPoly α
  AY2_t1 : UPoly α
  AY3_t0 : UPoly α
  AY3_t1 : UPoly α
  AX2_t0 : UPoly α
  AX2_t1 : UPoly α
  AX2_t2 : UPoly α
  Bv_SQ : UPoly α

def evalACache {α : Type*} (o : PolyOps α) (S Q : α) : ACache α :=
  letB (o.mul S S) fun S2 =>
  letB (o.mul S Q) fun SQ =>
  letB (o.mul Q Q) fun Q2 =>
  letB (o.mul S2 S) fun S3 =>
  letB (o.mul Q2 Q) fun Q3 =>
  letB (o.sub S (o.mul (o.ofInt 3) Q)) fun Sm3Q =>
  letB (o.mul Sm3Q Sm3Q) fun Sm3Q2 =>
  letB (o.sub (o.mul (o.ofInt 5) S) (o.mul (o.ofInt 9) Q)) fun A5 =>
  letB (o.mul (o.ofInt (-175)) (o.mul A5 (o.sub (o.mul (o.ofInt 5) S) (o.mul (o.ofInt 3) Q)))) fun ca0 =>
  letB (o.mul (o.ofInt 7) (o.add (o.sub (o.mul (o.ofInt 143) S2) (o.mul (o.ofInt 552) SQ)) (o.mul (o.ofInt 468) Q2))) fun ca1 =>
  letB (o.mul (o.ofInt (-28)) Sm3Q2) fun ca2 =>
  letB [ca0, ca1, ca2] fun ca_p =>
  letB (o.mul (o.ofInt 1050) (o.mul S A5)) fun cb0 =>
  letB (o.add (o.add (o.mul (o.ofInt 21) (o.sub (o.add (o.mul (o.ofInt (-92)) S2) (o.mul (o.ofInt 312) SQ))
      (o.mul (o.ofInt 198) Q2))) (o.mul (o.ofInt 810) Q)) (o.ofInt 810)) fun cb1 =>
  letB (o.mul (o.ofInt 84) Sm3Q2) fun cb2 =>
  letB [cb0, cb1, cb2] fun cb_p =>
  letB (uNeg o ca_p) fun b_p =>
  letB [o.sub cb0 (o.mul (o.ofInt 3) (o.neg ca0)), o.sub cb1 (o.mul (o.ofInt 3) (o.neg ca1))] fun am3b_p =>
  letB (uSub o (uSc o (o.ofInt 5) cb_p) (uSc o (o.ofInt 9) b_p)) fun a5m9b =>
  letB (uSub o (uSc o (o.ofInt 15) cb_p) (uSc o (o.ofInt 9) b_p)) fun a15m9b =>
  letB (uMul o cb_p cb_p) fun aa =>
  letB (uMul o cb_p b_p) fun ab =>
  letB (uMul o b_p b_p) fun bb =>
  letB (uMul o am3b_p am3b_p) fun am3b2 =>
  letB (uAdd o (uAdd o (uSc o (o.ofInt (-25)) (uMul o a5m9b a15m9b))
      (uShift o (uAdd o (uSub o (uSc o (o.ofInt 429) aa) (uSc o (o.ofInt 1656) ab)) (uSc o (o.ofInt 1404) bb))))
      (uShift o (uShift o (uSc o (o.ofInt (-12)) am3b2)))) fun A2 =>
  letB (uAdd o (uAdd o (uSc o (o.ofInt 50) (uMul o cb_p a5m9b))
      (uShift o (uSub o (uAdd o (uSc o (o.ofInt (-92)) aa) (uSc o (o.ofInt 312) ab)) (uSc o (o.ofInt 198) bb))))
      (uShift o (uShift o (uSc o (o.ofInt 4) am3b2)))) fun B2 =>
  letB (o.sub (o.mul (o.ofInt 15) S) (o.mul (o.ofInt 9) Q)) fun S15m9Q =>
  letB (uAdd o (uSc o S b_p) (uSc o Q cb_p)) fun sbqa =>
  letB (uAdd o (uAdd o (uSc o (o.ofInt (-25)) (uAdd o (uSc o S15m9Q a5m9b) (uSc o A5 a15m9b)))
      (uShift o (uAdd o (uSub o (uSc o (o.mul (o.ofInt 858) S) cb_p) (uSc o (o.ofInt 1656) sbqa))
        (uSc o (o.mul (o.ofInt 2808) Q) b_p))))
      (uShift o (uShift o (uSc o (o.mul (o.ofInt (-24)) Sm3Q) am3b_p)))) fun A1 =>
  letB (uAdd o (uAdd o (uSc o (o.ofInt 350) (uSub o (uSc o (o.sub (o.mul (o.ofInt 10) S) (o.mul (o.ofInt 9) Q)) cb_p)
      (uSc o (o.mul (o.ofInt 9) S) b_p)))
      (uShift o (uAdd o (uSc o (o.ofInt 7) (uSub o (uAdd o (uSc o (o.mul (o.ofInt (-184)) S) cb_p)
        (uSc o (o.ofInt 312) sbqa)) (uSc o (o.mul (o.ofInt 396) Q) b_p))) (uSc o (o.ofInt 270) b_p))))
      (uShift o (uShift o (uSc o (o.mul (o.ofInt 56) Sm3Q) am3b_p)))) fun B1 =>
  letB (uSc o (o.ofInt 567) (uSub o (uMul o A2 B1) (uSc o (o.ofInt 7) (uMul o A1 B2)))) fun D21 =>
  letB (uSub o (uSc o (o.ofInt 189) (uMul o A2 cb_p)) (uSc o (o.ofInt 1701) (uMul o ca_p B2))) fun D20 =>
  letB (uSub o (uSc o (o.ofInt 189) (uMul o A1 cb_p)) (uSc o (o.ofInt 243) (uMul o ca_p B1))) fun D10 =>
  letB (uAdd o (uSub o (uMul o aa D10) (uSc o (o.mul (o.ofInt 2) S) (uMul o cb_p D20))) (uSc o S2 D21)) fun m0 =>
  letB (uAdd o (uSub o (uMul o ab D10) (uMul o sbqa D20)) (uSc o SQ D21)) fun m1 =>
  letB (uAdd o (uSub o (uMul o bb D10) (uSc o (o.mul (o.ofInt 2) Q) (uMul o b_p D20))) (uSc o Q2 D21)) fun m2 =>
  letB (uSub o (uSc o S D21) (uMul o cb_p D20)) fun m4 =>
  letB (uSub o (uSc o Q D21) (uMul o b_p D20)) fun m6 =>
  letB (uSub o (uSc o (o.ofInt 5) m0) (uSc o (o.ofInt 9) m1)) fun l01 =>
  letB (uSub o (uSc o (o.ofInt 5) m1) (uSc o (o.ofInt 9) m2)) fun l12 =>
  letB (uSub o (uSc o (o.ofInt 5) m4) (uSc o (o.ofInt 9) m6)) fun l46 =>
  letB (uSc o (o.ofInt (-100 * 968178750)) l46) fun AY2_base =>
  letB (o.mul (o.ofInt (-175)) (o.mul S (o.mul A5 A5))) fun Bv0_1701 =>
  letB (o.sub (o.add (o.sub (o.mul (o.ofInt 143) S3) (o.mul (o.ofInt 828) (o.mul S2 Q)))
      (o.mul (o.ofInt 1404) (o.mul S Q2))) (o.mul (o.ofInt 594) Q3)) fun Bv1_243_S =>
  letB (o.add (o.add (o.mul (o.ofInt 7) Bv1_243_S) (o.mul (o.ofInt 1215) Q2)) (o.mul (o.ofInt 2430) Q)) fun Bv1_SQ_1701 =>
  letB (o.mul (o.ofInt (-28)) (o.mul Sm3Q2 Sm3Q)) fun Bv2_1701 =>
  ⟨ca_p, cb_p,
   uAdd o (uAdd o (uSc o (o.ofInt (-19708 * 187110)) l01) (uSc o (o.ofInt (1472 * 187110)) l12))
     (uSc o (o.ofInt (188 * 116181450)) l46),
   uSc o (o.ofInt (-16 * 322726250)) l46,
   uAdd o (uAdd o (uSc o (o.ofInt (-892 * (-9) * 64545250)) m4)
     (uSc o (o.ofInt (40 * (-9) * 2904536250)) m6)) (uSc o (o.ofInt (392 * (-9) * 19646550)) D21),
   uAdd o (uAdd o (uAdd o (uSc o (o.ofInt (-892 * 5 * 64545250)) m4)
     (uSc o (o.ofInt (40 * 5 * 2904536250)) m6)) (uSc o (o.ofInt (-112 * (-9) * 98232750)) D21))
     (uSc o (o.ofInt (392 * 5 * 19646550)) D21),
   uSc o (o.ofInt (-112 * 5 * 98232750)) D21,
   uSc o (o.ofInt (-9)) AY2_base,
   uSc o (o.ofInt 5) AY2_base,
   uAdd o (uSub o (uAdd o (uSc o (o.ofInt (-907876 * 6930)) l01) (uSc o (o.ofInt (2258324 * 6930)) l12))
     (uSc o (o.ofInt (64 * 348544350)) l46))
     (uShift o (uAdd o (uSc o (o.ofInt (-123236 * 126)) (uSub o (uAdd o (uSc o (o.ofInt 77) m0) (uSc o (o.ofInt 2790) m6)) (uSc o (o.ofInt 5904) D21)))
       (uSc o (o.ofInt (492944 * 9)) (uSub o (uAdd o (uSc o (o.ofInt 770) m1) (uSc o (o.ofInt 9270) m6)) (uSc o (o.ofInt 21159) D21))))),
   uAdd o (uSc o (o.ofInt (8 * 968178750)) l46)
     (uShift o (uAdd o (uSc o (o.ofInt (-123236 * 126)) (uSc o (o.ofInt 2156) D21))
       (uSc o (o.ofInt (492944 * 9)) (uSc o (o.ofInt 7546) D21)))),
   uShift o (uAdd o (uSc o (o.ofInt (-8 * (-9) * 580907250)) m4) (uSc o (o.ofInt (6916 * (-9) * 6548850)) D21)),
   uShift o (uAdd o (uAdd o (uSc o (o.ofInt (-8 * 5 * 580907250)) m4)
     (uSc o (o.ofInt (-476 * (-9) * 32744250)) D21)) (uSc o (o.ofInt (6916 * 5 * 6548850)) D21)),
   uShift o (uSc o (o.ofInt (-476 * 5 * 32744250)) D21),
   [Bv0_1701, Bv1_SQ_1701, Bv2_1701]⟩

structure GeomSQ (α : Type*) where
  H0_7_SQ : α
  S2 : α
  DX2 : BivL α
  dDX2_dS : BivL α
  dDX2_dQ : BivL α
  dDX2_dx : BivL α
  dF5_0 : BivL α
  dF5_1 : BivL α
  dF5_3 : BivL α
  LX_27 : UBivL α
  dLX_0 : UBivL α
  dLX_1 : UBivL α
  dLX_3 : UBivL α
  PX_0 : UBivL α
  PX_1 : UBivL α
  PX_3 : UBivL α
  A1_1_27 : UPoly α
  qC_63 : UPoly α
  qEx_63 : UPoly α

def evalGeomSQ {α : Type*} (o : PolyOps α) (S Q : α) : GeomSQ α :=
  letB (o.mul S S) fun S2 =>
  letB (o.mul S Q) fun SQ =>
  letB (o.mul Q Q) fun Q2 =>
  letB (o.mul S2 S) fun S3 =>
  letB (o.mul S2 S2) fun S4 =>
  letB (o.mul Q2 Q) fun Q3 =>
  letB (o.mul Q2 Q2) fun Q4 =>
  letB (o.sub S (o.mul (o.ofInt 3) Q)) fun Sm3Q =>
  letB (o.sub (o.mul (o.ofInt 5) S) (o.mul (o.ofInt 9) Q)) fun A5 =>
  letB (o.sub (o.sub (o.add (o.mul (o.ofInt (-2)) S3) (o.mul (o.ofInt 6) (o.mul S2 Q)))
      (o.mul (o.ofInt 3) (o.mul S Q2))) (o.mul (o.ofInt 2) Q3)) fun pS =>
  letB (o.add (o.add (o.mul (o.ofInt 7) pS) (o.mul (o.ofInt 5) Q2)) (o.mul (o.ofInt 10) Q)) fun H0_7_SQ =>
  letB ([[o.add (o.neg S) (o.mul (o.ofInt 2) Q)], [o.ofInt 1]] : BivL α) fun u3 =>
  letB (bivMul o u3 u3) fun u3_2 =>
  letB (bivConst (o.sub (o.mul (o.ofInt 25) S) (o.mul (o.ofInt 45) Q))) fun LX0 =>
  letB ([[o.sub (o.mul (o.ofInt 45) Q) (o.mul (o.ofInt 25) S)], [o.ofInt 27]] : BivL α) fun LX1 =>
  letB ([LX0, LX1] : UBivL α) fun LX_27 =>
  letB ([bivConst (o.ofInt 25), bivConst (o.ofInt (-25))] : UBivL α) fun dLX_0 =>
  letB ([bivConst (o.ofInt (-45)), bivConst (o.ofInt 45)] : UBivL α) fun dLX_1 =>
  letB ([[], bivConst (o.ofInt 27)] : UBivL α) fun dLX_3 =>
  letB (o.mul (o.ofInt 2) S) fun S2x =>
  ⟨H0_7_SQ, S2,
   bivAdd o (bivConst (o.sub (o.mul S Q2) (o.mul (o.ofInt 4) Q3)))
     (bivAdd o (bivSc o (o.sub (o.mul (o.ofInt 18) SQ) (o.mul (o.ofInt 4) S2)) u3)
       (bivSc o (o.mul (o.ofInt (-27)) S) u3_2)),
   bivAdd o (bivConst (o.sub (o.add Q2 (o.mul (o.ofInt 4) S2)) (o.mul (o.ofInt 18) SQ)))
     (bivAdd o (bivSc o (o.add (o.mul (o.ofInt 46) S) (o.mul (o.ofInt 18) Q)) u3)
       (bivSc o (o.ofInt (-27)) u3_2)),
   bivAdd o (bivConst (o.sub (o.add (o.mul (o.ofInt (-8)) S2) (o.mul (o.ofInt 38) SQ)) (o.mul (o.ofInt 12) Q2)))
     (bivSc o (o.mul (o.ofInt (-90)) S) u3),
   bivAdd o (bivConst (o.add (o.mul (o.ofInt (-4)) S2) (o.mul (o.ofInt 18) SQ)))
     (bivSc o (o.mul (o.ofInt (-54)) S) u3),
   [[o.mul (o.ofInt 7) (o.sub (o.add (o.mul (o.ofInt (-6)) S2) (o.mul (o.ofInt 12) SQ)) (o.mul (o.ofInt 3) Q2))], [], [o.ofInt 21]],
   [[o.add (o.add (o.mul (o.ofInt 7) (o.sub (o.sub (o.mul (o.ofInt 6) S2) (o.mul (o.ofInt 6) SQ)) (o.mul (o.ofInt 6) Q2)))
     (o.mul (o.ofInt 10) Q)) (o.ofInt 10)]],
   [[], [o.mul (o.ofInt 42) S]],
   LX_27, dLX_0, dLX_1, dLX_3,
   ubAdd o (ubSc o S2x dLX_0) LX_27, ubSc o S2x dLX_1, ubSc o S2x dLX_3,
   [o.mul (o.ofInt 25) (o.mul S (o.mul A5 A5)), o.mul (o.ofInt (-4)) (o.mul (o.mul Sm3Q Sm3Q) Sm3Q)],
   [o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add
      (o.mul (o.ofInt (-5250)) S4) (o.mul (o.ofInt 30450) (o.mul S3 Q)))
      (o.mul (o.ofInt (-64050)) (o.mul S2 Q2))) (o.mul (o.ofInt 63000) (o.mul S Q3)))
      (o.mul (o.ofInt (-28350)) Q4)) (o.mul (o.ofInt 6250) (o.mul S2 Q)))
      (o.mul (o.ofInt (-15000)) (o.mul S Q2))) (o.mul (o.ofInt 6750) Q3))
      (o.mul (o.ofInt 6250) S2)) (o.mul (o.ofInt (-15000)) SQ)) (o.mul (o.ofInt 6750) Q2),
    o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add (o.add
      (o.mul (o.ofInt 336) S4) (o.mul (o.ofInt (-2856)) (o.mul S3 Q)))
      (o.mul (o.ofInt 8484) (o.mul S2 Q2))) (o.mul (o.ofInt (-10080)) (o.mul S Q3)))
      (o.mul (o.ofInt 3780) Q4)) (o.mul (o.ofInt (-40)) (o.mul S2 Q)))
      (o.mul (o.ofInt 240) (o.mul S Q2))) (o.mul (o.ofInt (-360)) Q3))
      (o.mul (o.ofInt (-40)) S2)) (o.mul (o.ofInt 240) SQ)) (o.mul (o.ofInt (-360)) Q2)],
   [o.add (o.add (o.add (o.add (o.add (o.add (o.add
      (o.mul (o.ofInt 6090) S3) (o.mul (o.ofInt (-25620)) (o.mul S2 Q)))
      (o.mul (o.ofInt 34650) (o.mul S Q2))) (o.mul (o.ofInt (-20790)) Q3))
      (o.mul (o.ofInt (-6750)) SQ)) (o.mul (o.ofInt 4050) Q2))
      (o.mul (o.ofInt (-6750)) S)) (o.mul (o.ofInt 4050) Q),
    o.add (o.add (o.add
      (o.mul (o.ofInt (-420)) S3) (o.mul (o.ofInt 2940) (o.mul S2 Q)))
      (o.mul (o.ofInt (-6300)) (o.mul S Q2))) (o.mul (o.ofInt 3780) Q3)]⟩


structure GeomT (α : Type*) where
  H0_7 : α
  H0_7_2 : α
  Av0_243 : α
  Cv0_int : α
  Cv0_243 : α
  Bv1_T_1701 : α
  DY2 : BivL α
  rem_qX0 : BivL α
  rem_qX1 : BivL α
  qX_0_sc : UBivL α
  qX_1_sc : UBivL α
  qY_0_321489 : UBivL α
  DY2_qE_63 : UBivL α
  q1_0_div_sc : UBivL α
  q1_1_sc : UBivL α
  q1_2_div_sc : UBivL α

def evalGeomT {α : Type*} (o : PolyOps α) (S : α) (ca_p cb_p : UPoly α) (gsq : GeomSQ α) (T : α) : GeomT α :=
  letB (o.mul T T) fun T2 =>
  letB (o.mul T2 T) fun T3 =>
  letB (o.sub (o.sub (o.add (o.mul (o.ofInt (-2)) T3) (o.mul (o.ofInt 6) T2)) (o.mul (o.ofInt 3) T)) (o.ofInt 2)) fun pT =>
  letB (o.add gsq.H0_7_SQ (o.mul (o.ofInt 7) pT)) fun H0_7 =>
  letB (o.mul H0_7 H0_7) fun H0_7_2 =>
  letB (o.sub T (o.ofInt 3)) fun Tm3 =>
  letB (o.mul (o.ofInt (-4)) (o.mul (o.mul Tm3 Tm3) Tm3)) fun Av0_243 =>
  letB (o.sub (o.mul (o.ofInt 5) T) (o.ofInt 9)) fun T59 =>
  letB (o.mul T (o.mul T59 T59)) fun Cv0_int =>
  letB (o.mul (o.ofInt (-25)) Cv0_int) fun Cv0_243 =>
  letB (o.mul (o.ofInt 7) (o.sub (o.add (o.sub (o.mul (o.ofInt 143) T3) (o.mul (o.ofInt 828) T2))
      (o.mul (o.ofInt 1404) T)) (o.ofInt 594))) fun Bv1_T_1701 =>
  letB ([[o.add (o.neg T) (o.ofInt 2), o.ofInt 1]] : BivL α) fun v3 =>
  letB (bivMul o v3 v3) fun v3_2 =>
  letB (bivAdd o (bivConst (o.sub T (o.ofInt 4)))
      (bivAdd o (bivSc o (o.sub (o.mul (o.ofInt 18) T) (o.mul (o.ofInt 4) T2)) v3)
        (bivSc o (o.mul (o.ofInt (-27)) T) v3_2))) fun DY2 =>
  letB (bivAdd o (bivConst (o.add (o.mul (o.ofInt (-4)) T2) (o.mul (o.ofInt 18) T)))
      (bivSc o (o.mul (o.ofInt (-54)) T) v3)) fun dDY2_dy =>
  letB (o.mul S T) fun ST =>
  letB (o.mul (o.ofInt 2) ST) fun ST2 =>
  letB (bivSc o ST (bivMul o gsq.DX2 DY2)) fun W2 =>
  letB ([[o.zero, o.mul (o.ofInt 42) T]] : BivL α) fun dF5_4 =>
  letB (bivConst (o.sub (o.mul (o.ofInt 25) T) (o.ofInt 45))) fun LY0 =>
  letB ([[o.sub (o.ofInt 45) (o.mul (o.ofInt 25) T), o.ofInt 27]] : BivL α) fun LY1 =>
  letB (bivConst (o.mul (o.ofInt 54) T)) fun PY_4_1 =>
  letB (ubSub o (ubSc o (o.neg ST2) (ubBmul o LY0 gsq.dLX_0)) (ubSc o T (ubBmul o LY0 gsq.LX_27))) fun br0_0 =>
  letB (ubSub o (ubSc o (o.neg ST2) (ubBmul o LY1 gsq.dLX_0)) (ubSc o T (ubBmul o LY1 gsq.LX_27))) fun br1_0 =>
  letB (ubSc o (o.neg ST2) (ubBmul o LY0 gsq.dLX_1)) fun br0_1 =>
  letB (ubSc o (o.neg ST2) (ubBmul o LY1 gsq.dLX_1)) fun br1_1 =>
  letB (ubSc o (o.neg ST2) (ubBmul o LY0 gsq.dLX_3)) fun br0_3 =>
  letB (ubSc o (o.neg ST2) (ubBmul o LY1 gsq.dLX_3)) fun br1_3 =>
  letB (ubSc o (o.mul (o.ofInt 27) ST2) gsq.LX_27) fun br1_4 =>
  letB (ubSc o ST (ubAdd o (ubBmul o gsq.dF5_3 (ubNeg o (ubBmul o PY_4_1 gsq.PX_0)))
      (ubBmul o gsq.dF5_0 (ubBmul o PY_4_1 gsq.PX_3)))) fun omF1_0 =>
  letB (ubSc o ST (ubAdd o (ubBmul o gsq.dF5_3 (ubNeg o (ubBmul o PY_4_1 gsq.PX_1)))
      (ubBmul o gsq.dF5_1 (ubBmul o PY_4_1 gsq.PX_3)))) fun omF1_1 =>
  letB (ubSc o ST (ubSub o (ubBmul o gsq.dF5_3 (ubBmul o dDY2_dy br0_0)) (ubBmul o gsq.dF5_0 (ubBmul o dDY2_dy br0_3)))) fun dYF0_0 =>
  letB (ubSc o ST (ubSub o (ubBmul o gsq.dF5_3 (ubBmul o dDY2_dy br0_1)) (ubBmul o gsq.dF5_1 (ubBmul o dDY2_dy br0_3)))) fun dYF0_1 =>
  letB (ubSc o ST (ubSub o (ubBmul o gsq.dF5_3 (ubBmul o dDY2_dy br1_0)) (ubBmul o gsq.dF5_0 (ubBmul o dDY2_dy br1_3)))) fun dYF1_0 =>
  letB (ubSc o ST (ubSub o (ubBmul o gsq.dF5_3 (ubBmul o dDY2_dy br1_1)) (ubBmul o gsq.dF5_1 (ubBmul o dDY2_dy br1_3)))) fun dYF1_1 =>
  letB (ubSc o ST (ubBmul o dF5_4 (ubSub o (ubBmul o gsq.dDX2_dS br0_3) (ubBmul o gsq.dDX2_dx br0_0)))) fun dXF0_0 =>
  letB (ubSc o ST (ubBmul o dF5_4 (ubSub o (ubBmul o gsq.dDX2_dQ br0_3) (ubBmul o gsq.dDX2_dx br0_1)))) fun dXF0_1 =>
  letB (ubBmul o gsq.DX2 dYF0_0) fun QX0_0 =>
  letB (ubBmul o gsq.DX2 dYF0_1) fun QX0_1 =>
  letB (ubBmul o gsq.DX2 (ubSub o dYF1_0 (ubBmul o DY2 omF1_0))) fun QX1_0 =>
  letB (ubBmul o gsq.DX2 (ubSub o dYF1_1 (ubBmul o DY2 omF1_1))) fun QX1_1 =>
  letB (ubNeg o (ubBmul o DY2 dXF0_0)) fun QY0_0 =>
  letB (ubNeg o (ubBmul o DY2 dXF0_1)) fun QY0_1 =>
  letB (ubSc o (o.ofInt 2) (ubBmul o W2 (ubBmul o dF5_4 br0_3))) fun EB0_5103 =>
  letB (ubSc o (o.ofInt 2) (ubBmul o W2 (ubSub o (ubBmul o dF5_4 br1_3) (ubBmul o gsq.dF5_3 br1_4)))) fun EB1_5103 =>
  letB (ubSynDiv1Rem o (ubSub o (ubMulU o cb_p QX0_0) (ubMulU o ca_p QX0_1))) fun div0 =>
  letB (ubSynDiv1Rem o (ubSub o (ubMulU o cb_p QX1_0) (ubMulU o ca_p QX1_1))) fun div1 =>
  letB (ubSub o (ubMulU o cb_p QY0_0) (ubMulU o ca_p QY0_1)) fun QY_dot_0_sc =>
  letB (o.mul (o.ofInt 4) (o.mul gsq.S2 T2)) fun c4S2T2 =>
  letB ([[[o.mul c4S2T2 (gsq.qC_63.getD 0 o.zero)], [o.mul c4S2T2 (gsq.qEx_63.getD 0 o.zero)]],
         [[o.mul c4S2T2 (gsq.qC_63.getD 1 o.zero)], [o.mul c4S2T2 (gsq.qEx_63.getD 1 o.zero)]]] : UBivL α) fun qE_63 =>
  letB (ubBmul o DY2 qE_63) fun DY2_qE_63 =>
  letB (ubAdd o (ubNeg o QY_dot_0_sc) (ubSc o (o.mul (o.ofInt 189) Cv0_243) (ubShift DY2_qE_63))) fun qY_0_321489 =>
  ⟨H0_7, H0_7_2, Av0_243, Cv0_int, Cv0_243, Bv1_T_1701, DY2,
   div0.1, div1.1, div0.2, div1.2, qY_0_321489, DY2_qE_63,
   ubAdd o (ubSc o (o.mul (o.ofInt (-9)) H0_7) div0.2) (ubSc o (o.ofInt 63) (ubMulU o gsq.qC_63 EB0_5103)),
   ubAdd o (ubSc o (o.mul (o.ofInt 9) H0_7) (ubMulU o gsq.A1_1_27 qY_0_321489))
     (ubShift (ubAdd o
       (ubSc o (o.mul (o.ofInt 9) H0_7) (ubSub o (ubSc o Av0_243 div0.2) (ubSc o Cv0_243 div1.2)))
       (ubSc o (o.ofInt 63) (ubMulU o gsq.qC_63 (ubSub o (ubSc o Cv0_243 EB1_5103) (ubSc o Av0_243 EB0_5103)))))),
   ubSub o
     (ubAdd o (ubSc o (o.mul (o.ofInt (-1701)) H0_7) (ubMulU o gsq.A1_1_27 DY2_qE_63))
       (ubSc o (o.mul (o.ofInt 9) H0_7) div1.2))
     (ubSc o (o.ofInt 63) (ubMulU o gsq.qC_63 EB1_5103))⟩


section GeomRelDefs
variable {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
structure ACacheRel (R : α → β → Prop) (a : ACache α) (b : ACache β) : Prop where
  ca_p : URel R a.ca_p b.ca_p
  cb_p : URel R a.cb_p b.cb_p
  A0U_t0 : URel R a.A0U_t0 b.A0U_t0
  A0U_t1 : URel R a.A0U_t1 b.A0U_t1
  A0V_t0 : URel R a.A0V_t0 b.A0V_t0
  A0V_t1 : URel R a.A0V_t1 b.A0V_t1
  A0V_t2 : URel R a.A0V_t2 b.A0V_t2
  AY2_t0 : URel R a.AY2_t0 b.AY2_t0
  AY2_t1 : URel R a.AY2_t1 b.AY2_t1
  AY3_t0 : URel R a.AY3_t0 b.AY3_t0
  AY3_t1 : URel R a.AY3_t1 b.AY3_t1
  AX2_t0 : URel R a.AX2_t0 b.AX2_t0
  AX2_t1 : URel R a.AX2_t1 b.AX2_t1
  AX2_t2 : URel R a.AX2_t2 b.AX2_t2
  Bv_SQ : URel R a.Bv_SQ b.Bv_SQ

structure GeomSQRel (R : α → β → Prop) (a : GeomSQ α) (b : GeomSQ β) : Prop where
  H0_7_SQ : R a.H0_7_SQ b.H0_7_SQ
  S2 : R a.S2 b.S2
  DX2 : BRel R a.DX2 b.DX2
  dDX2_dS : BRel R a.dDX2_dS b.dDX2_dS
  dDX2_dQ : BRel R a.dDX2_dQ b.dDX2_dQ
  dDX2_dx : BRel R a.dDX2_dx b.dDX2_dx
  dF5_0 : BRel R a.dF5_0 b.dF5_0
  dF5_1 : BRel R a.dF5_1 b.dF5_1
  dF5_3 : BRel R a.dF5_3 b.dF5_3
  LX_27 : UBRel R a.LX_27 b.LX_27
  dLX_0 : UBRel R a.dLX_0 b.dLX_0
  dLX_1 : UBRel R a.dLX_1 b.dLX_1
  dLX_3 : UBRel R a.dLX_3 b.dLX_3
  PX_0 : UBRel R a.PX_0 b.PX_0
  PX_1 : UBRel R a.PX_1 b.PX_1
  PX_3 : UBRel R a.PX_3 b.PX_3
  A1_1_27 : URel R a.A1_1_27 b.A1_1_27
  qC_63 : URel R a.qC_63 b.qC_63
  qEx_63 : URel R a.qEx_63 b.qEx_63

structure GeomTRel (R : α → β → Prop) (a : GeomT α) (b : GeomT β) : Prop where
  H0_7 : R a.H0_7 b.H0_7
  H0_7_2 : R a.H0_7_2 b.H0_7_2
  Av0_243 : R a.Av0_243 b.Av0_243
  Cv0_int : R a.Cv0_int b.Cv0_int
  Cv0_243 : R a.Cv0_243 b.Cv0_243
  Bv1_T_1701 : R a.Bv1_T_1701 b.Bv1_T_1701
  DY2 : BRel R a.DY2 b.DY2
  rem_qX0 : BRel R a.rem_qX0 b.rem_qX0
  rem_qX1 : BRel R a.rem_qX1 b.rem_qX1
  qX_0_sc : UBRel R a.qX_0_sc b.qX_0_sc
  qX_1_sc : UBRel R a.qX_1_sc b.qX_1_sc
  qY_0_321489 : UBRel R a.qY_0_321489 b.qY_0_321489
  DY2_qE_63 : UBRel R a.DY2_qE_63 b.DY2_qE_63
  q1_0_div_sc : UBRel R a.q1_0_div_sc b.q1_0_div_sc
  q1_1_sc : UBRel R a.q1_1_sc b.q1_1_sc
  q1_2_div_sc : UBRel R a.q1_2_div_sc b.q1_2_div_sc

end GeomRelDefs

lemma uAdd_len {α : Type*} (o : PolyOps α) : ∀ a b, (uAdd o a b).length = max a.length b.length
  | [], b => by simp [uAdd]
  | a :: as, [] => by simp [uAdd]
  | _ :: as, _ :: bs => by simp [uAdd, uAdd_len o as bs, Nat.succ_max_succ]

lemma uSub_len {α : Type*} (o : PolyOps α) : ∀ a b, (uSub o a b).length = max a.length b.length
  | [], b => by simp [uSub, uNeg]
  | a :: as, [] => by simp [uSub]
  | _ :: as, _ :: bs => by simp [uSub, uSub_len o as bs, Nat.succ_max_succ]

lemma uMul_len_le {α : Type*} (o : PolyOps α) :
    ∀ a b, b ≠ [] → (uMul o a b).length ≤ a.length + b.length - 1
  | [], _, _ => by simp [uMul]
  | [x], b, hb => by
      simp only [uMul, uAdd_len, uSc, uShift, List.length_map, List.length_cons, List.length_nil]
      have : 1 ≤ b.length := List.length_pos_of_ne_nil hb
      omega
  | x :: y :: xs, b, hb => by
      have ih := uMul_len_le o (y :: xs) b hb
      simp only [uMul, uAdd_len, uSc, uShift, List.length_map, List.length_cons] at ih ⊢
      omega

lemma ubAdd_len {α : Type*} (o : PolyOps α) : ∀ a b, (ubAdd o a b).length = max a.length b.length
  | [], b => by simp [ubAdd]
  | a :: as, [] => by simp [ubAdd]
  | _ :: as, _ :: bs => by simp [ubAdd, ubAdd_len o as bs, Nat.succ_max_succ]

lemma ubSub_len {α : Type*} (o : PolyOps α) : ∀ a b, (ubSub o a b).length = max a.length b.length
  | [], b => by simp [ubSub, ubNeg]
  | a :: as, [] => by simp [ubSub]
  | _ :: as, _ :: bs => by simp [ubSub, ubSub_len o as bs, Nat.succ_max_succ]

lemma ubMulU_len_le {α : Type*} (o : PolyOps α) :
    ∀ u b, b ≠ [] → (ubMulU o u b).length ≤ u.length + b.length - 1
  | [], _, _ => by simp [ubMulU]
  | [c], b, hb => by
      simp only [ubMulU, ubAdd_len, ubSc, ubShift, List.length_map, List.length_cons, List.length_nil]
      have : 1 ≤ b.length := List.length_pos_of_ne_nil hb
      omega
  | c :: c' :: cs, b, hb => by
      have ih := ubMulU_len_le o (c' :: cs) b hb
      simp only [ubMulU, ubAdd_len, ubSc, ubShift, List.length_map, List.length_cons] at ih ⊢
      omega

lemma ubSynDiv1Rem_len {α : Type*} (o : PolyOps α) :
    ∀ a, (ubSynDiv1Rem o a).2.length = a.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: b' :: rest => by
      have ih := ubSynDiv1Rem_len o (b' :: rest)
      simp only [ubSynDiv1Rem, List.length_cons] at ih ⊢
      omega

lemma uSc_len {α : Type*} (o : PolyOps α) (c : α) (a : UPoly α) : (uSc o c a).length = a.length :=
  List.length_map _

def acUnit : ACache Unit := evalACache uOps () ()
def gsqUnit : GeomSQ Unit := evalGeomSQ uOps () ()
def gtUnit : GeomT Unit := evalGeomT uOps () acUnit.ca_p acUnit.cb_p gsqUnit ()


end SymmetricSexticResidual.LocalResidueQ5


