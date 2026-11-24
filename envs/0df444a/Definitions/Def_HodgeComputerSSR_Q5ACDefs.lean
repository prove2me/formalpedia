-- Prove2me | Definitions.Def_HodgeComputerSSR_Q5ACDefs
-- name    : HodgeComputerSSR_Q5ACDefs
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T22:08:45.274282+00:00
-- url     : https://prove2.me/theorems/f8a6cba7-e143-48bb-8add-33ed55b204ce
-- title:
--   $Q_{23}$ decomposition of $\eta_{A_C}$ and $A_C$/geometric bridge specifications
-- statement:
--   Defines the $Q_{23}$ split $\eta_{A_C} = \eta_{A_C,\mathrm{main}} + \eta_{A_C,\mathrm{reg}}$ and states the symbolic bridge specs `Q5ACBridgeSpec` and `Q5GeomBridgeSpec` without importing `Q5Weights` or `RQ5Biv`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Alg.lean#L1165-L1228

import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_Q5K5Geom

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueU0 QuadraticCovers
  CrossedRationalResidue Polynomial PolynomialEncoding.KroneckerCheck
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

def Q23_of {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 p4 p3 p2 p1 p0 : R) : R :=
  - q0 ^ 2 * e2 ^ 2 * p4
  + q0 ^ 2 * e3 * e1 * p4
  + q0 ^ 2 * e3 * e2 * p3
  - q0 ^ 2 * e3 ^ 2 * p2
  + q1 * q0 * e2 * e1 * p4
  - q1 * q0 * e3 * e0 * p4
  - q1 * q0 * e3 * e1 * p3
  + q1 * q0 * e3 ^ 2 * p1
  - q1 ^ 2 * e2 * e0 * p4
  + q1 ^ 2 * e3 * e0 * p3
  - q1 ^ 2 * e3 ^ 2 * p0
  - q2 * q0 * e1 ^ 2 * p4
  + 2 * q2 * q0 * e2 * e0 * p4
  - q2 * q0 * e3 * e0 * p3
  + q2 * q0 * e3 * e1 * p2
  - q2 * q0 * e3 * e2 * p1
  + q2 * q0 * e3 ^ 2 * p0
  + q2 * q1 * e1 * e0 * p4
  - q2 * q1 * e3 * e0 * p2
  + q2 * q1 * e3 * e2 * p0
  - q2 ^ 2 * e0 ^ 2 * p4
  + q2 ^ 2 * e3 * e0 * p1
  - q2 ^ 2 * e3 * e1 * p0

lemma Q5_rem_split {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 p4 p3 p2 p1 p0 : R) :
    e3 * (remDeg4_P1 q2 q1 q0 p4 p3 p2 p1 * remDeg3_d0 q2 q1 q0 e3 e2 e0 -
          remDeg4_P0 q2 q1 q0 p4 p3 p2 p0 * remDeg3_d1 q2 q1 q0 e3 e2 e1) =
    q2 ^ 2 * p4 * syl5 q2 q1 q0 e3 e2 e1 e0 +
    q2 ^ 3 * Q23_of q2 q1 q0 e3 e2 e1 e0 p4 p3 p2 p1 p0 := by
  simp only [remDeg4_P1, remDeg4_P0, remDeg3_d1, remDeg3_d0, syl5, Q23_of]
  ring

def p4_AC : A_C := (interp4 P18_z_AC).1

def Q23_AC : A_C :=
  let p := interp4 P18_z_AC
  Q23_of (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
    (pairC k5Params.d3_3) (pairC k5Params.d3_2) (pairC k5Params.d3_1) (pairC k5Params.d3_0)
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

def eta_AC_main : A_C :=
  -(p4_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
    (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q7_z * polyC k5Params.Q5_z)

def eta_AC_reg : A_C :=
  -(Q23_AC * U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4) /
    (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q7_z * pairC k5Params.res_z)

lemma Q7_K5_ne_zero : k5Params.Q7_z ≠ 0 := by
  intro h0
  obtain ⟨u, v, huv⟩ := isCoprime_Q5_Q7
  rw [h0, mul_zero, add_zero] at huv
  have hdeg := congrArg Polynomial.natDegree huv
  rw [Polynomial.natDegree_one] at hdeg
  have hu : u ≠ 0 := fun hu0 => by simp [hu0] at huv
  rw [Polynomial.natDegree_mul hu Q5_K5_ne_zero, Q5_K5_natDegree] at hdeg
  omega


lemma mapRatFunc_toRat (P : K5[X]) :
    mapRatFunc ιL_K5 (toRat P) = algebraMap CoverL[X] (RatFunc CoverL) (P.map ιL_K5) :=
  mapRatFunc_algebraMap ιL_K5 P


lemma F5_of_K5_zero : F5_of S_K Q_K T_K x_K y_K = 0 := by
  have h := F5_of_L (L := K5)
  simpa only [F5_of, H0_of, SL, QL, TL, xL, yL, ιL, Algebra.algebraMap_self, RingHom.id_apply] using h

lemma evalBivLK5_bivRedOnce (b : BivL K5) :
    evalBivLK5 (bivRedOnce k5Ops (21 * S_K) (-(21 * T_K)) (-(7 * H0_of S_K Q_K T_K)) b) =
      (21 * S_K) * evalBivLK5 b := by
  have hx2 : 21 * S_K * x_K ^ 2 = -(21 * T_K) * y_K ^ 2 + -(7 * H0_of S_K Q_K T_K) := by
    have hF := F5_of_K5_zero; unfold F5_of at hF; linear_combination 7 * hF
  exact evalBivL_bivRedOnce hx2 b


section NumMLead3
variable {R : Type*} [Field R] [CharZero R]

def numM_lead3 (mi : Fin 10) (S Q T a1 b1 U V : R) : R :=
  let a2 := q1_a2 a1 b1 U V; let a1' := q1_a1 a1 b1 S Q U V; let a0' := q1_a0 S Q U V
  let b2 := q2_b2 a1 b1 U V; let b1' := q2_b1 a1 b1 S Q U V; let b0' := q2_b0 S Q U V
  let d21 := a2 * b1' - a1' * b2
  let d20 := a2 * b0' - a0' * b2
  let d10 := a1' * b0' - a0' * b1'
  (1 / 16) * match mi with
    | 0 => a1 ^ 2 * d10 - 2 * a1 * S * d20 + S ^ 2 * d21
    | 1 => a1 * b1 * d10 - (a1 * Q + b1 * S) * d20 + S * Q * d21
    | 2 => b1 ^ 2 * d10 - 2 * b1 * Q * d20 + Q ^ 2 * d21
    | 3 => T * (S * d21 - a1 * d20)
    | 4 => S * d21 - a1 * d20
    | 5 => T * (Q * d21 - b1 * d20)
    | 6 => Q * d21 - b1 * d20
    | 7 => T ^ 2 * d21
    | 8 => T * d21
    | 9 => d21

end NumMLead3

lemma polyC_C (c : K5) : polyC (Polynomial.C c) = ιC_K5 c := by
  simp [polyC, ιC_K5, toRat]

lemma polyC_X : polyC (Polynomial.X : K5[X]) = U_C := by
  simp [polyC, U_C, toRat]

lemma polyC_add (p q : K5[X]) : polyC (p + q) = polyC p + polyC q := by
  simp [polyC]

lemma polyC_sub (p q : K5[X]) : polyC (p - q) = polyC p - polyC q := by
  simp [polyC]

lemma polyC_neg (p : K5[X]) : polyC (-p) = -polyC p := by
  simp [polyC]

lemma polyC_mul (p q : K5[X]) : polyC (p * q) = polyC p * polyC q := by
  simp [polyC]

lemma polyC_pow (p : K5[X]) (n : ℕ) : polyC (p ^ n) = polyC p ^ n := by
  simp [polyC]

lemma polyC_zero : polyC 0 = 0 := by simp only [polyC, toRat, map_zero]
lemma polyC_one : polyC 1 = 1 := by simp only [polyC, toRat, map_one]
lemma polyC_ofNat (n : ℕ) [n.AtLeastTwo] : polyC (no_index (OfNat.ofNat n)) = OfNat.ofNat n := by
  simp only [polyC, toRat, map_ofNat]

lemma polyC_ca_cb_eq_q10_q20 :
    polyC k5Params.ca_h = q1_a0 (ιC_K5 S_K) (ιC_K5 Q_K) U_C 1 ∧
    polyC k5Params.cb_h = q2_b0 (ιC_K5 S_K) (ιC_K5 Q_K) U_C 1 := by
  constructor <;> (
    simp only [CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, 
      map_add, map_sub, map_mul, map_inv₀, map_neg, map_pow, map_ofNat,
      q1_a0, q2_b0, dH_dS, dH_dQ]; ring)


/-- Bundled `acK` algebraic bridge properties over `A_C` (without `Q5Weights` or `RQ5Biv`). -/
structure Q5ACBridgeSpec : Prop where
  ca_p : evalUPolyK5 acK.ca_p = Polynomial.C 567 * k5Params.ca_h
  cb_p : evalUPolyK5 acK.cb_p = Polynomial.C 567 * k5Params.cb_h
  ca_e0 : (evalUPolyK5 acK.ca_p).eval 0 = -175 * ((5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K))
  cb_e0 : (evalUPolyK5 acK.cb_p).eval 0 = 1050 * (S_K * (5 * S_K - 9 * Q_K))
  AY2_e0 : (evalUPolyK5 acK.AY2_t0).eval 0 = 0 ∧ (evalUPolyK5 acK.AY2_t1).eval 0 = 0
  AX2_e0 : (evalUPolyK5 acK.AX2_t0).eval 0 = 0 ∧ (evalUPolyK5 acK.AX2_t1).eval 0 = 0 ∧ (evalUPolyK5 acK.AX2_t2).eval 0 = 0
  Bv_SQ : polyC (evalUPolyK5 acK.Bv_SQ) =
    ιC_K5 (-175 * (S_K * (5 * S_K - 9 * Q_K) ^ 2)) +
    U_C * ιC_K5 (7 * (143 * S_K ^ 3 - 828 * S_K ^ 2 * Q_K + 1404 * S_K * Q_K ^ 2 - 594 * Q_K ^ 3) +
      1215 * Q_K ^ 2 + 2430 * Q_K) +
    U_C ^ 2 * ιC_K5 (-28 * (S_K - 3 * Q_K) ^ 3)
  ac_bridge :
    let m := fun mi : Fin 10 => numM_lead3 mi (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K)
      (polyC k5Params.cb_h) (-polyC k5Params.ca_h) U_C 1
    let MA : A_C := (M_A_int : A_C)
    (U_C * polyC A0U_U_p = MA * (-(19708 / 1257375 : A_C) * (5 * m 0 - 9 * m 1) +
        (1472 / 1257375 : A_C) * (5 * m 1 - 9 * m 2) - (16 / 729 : A_C) * (5 * m 3 - 9 * m 5) +
        (188 / 2025 : A_C) * (5 * m 4 - 9 * m 6))) ∧
    (polyC A0V_p = MA * (-(892 / 3645 : A_C) * (5 * m 3 - 9 * m 4) + (40 / 81 : A_C) * (5 * m 5 - 9 * m 6) -
        (112 / 2395 : A_C) * (5 * m 7 - 9 * m 8) + (392 / 11975 : A_C) * (5 * m 8 - 9 * m 9))) ∧
    (polyC AY2_p = MA * (-(100 / 243 : A_C) * (25 * m 3 - 45 * m 4 - 45 * m 5 + 81 * m 6))) ∧
    (polyC AY3_p = MA * (-(907876 / 33949125 : A_C) * (5 * m 0 - 9 * m 1) +
        (2258324 / 33949125 : A_C) * (5 * m 1 - 9 * m 2) + (8 / 243 : A_C) * (5 * m 3 - 9 * m 5) -
        (64 / 675 : A_C) * (5 * m 4 - 9 * m 6) +
        U_C * (-(123236 / 24249375 : A_C) * (m 0 + (2790 / 77 : A_C) * m 6 + 28 * m 8 - (5904 / 77 : A_C) * m 9) +
          (492944 / 33949125 : A_C) * (m 1 + (927 / 77 : A_C) * m 6 + (49 / 5 : A_C) * m 8 - (21159 / 770 : A_C) * m 9)))) ∧
    (polyC AX2_p = MA * (U_C * (-(8 / 405 : A_C) * (5 * m 3 - 9 * m 4) -
        (476 / 7185 : A_C) * (5 * m 7 - 9 * m 8) + (6916 / 35925 : A_C) * (5 * m 8 - 9 * m 9))))

/-- Bundled `gtK` geometric bridge properties over `A_C` (without `Q5Weights` or `RQ5Biv`). -/
structure Q5GeomBridgeSpec : Prop where
  gt_props :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K
    let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let ca := polyC k5Params.ca_h; let cb := polyC k5Params.cb_h
    let QX_dot := QX_num S Q T x y U_C V_C 0 * cb - QX_num S Q T x y U_C V_C 1 * ca
    let QY_dot := QY_num S Q T x y U_C V_C 0 * cb - QY_num S Q T x y U_C V_C 1 * ca
    let cA1_dot := (H0_of S Q T * dA1_fn 0 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 0 S Q T) * cb -
      (H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * ca
    let q1_dot := H0_of S Q T * A1_of S Q U_C V_C * (QY_dot / v_of V_C) +
      H0_of S Q T * B1_of T U_C V_C * (QX_dot / u_of U_C) +
      (cA1_dot / v_of V_C) * EB_of S Q T x y U_C V_C
    (gtK.H0_7 = 7 * H0_of S_K Q_K T_K) ∧
    (gtK.H0_7_2 = gtK.H0_7 ^ 2) ∧
    (gtK.Av0_243 = 243 * k5Params.Av0) ∧
    (gtK.Cv0_243 = 243 * k5Params.Cv0) ∧
    (gtK.Cv0_243 = -25 * gtK.Cv0_int) ∧
    (polyC Bv_1701_p = 1701 * (ιC_K5 k5Params.Av0 * polyC k5Params.bW)) ∧
    (polyC (evalUBivLK5 gtK.qX_0_sc) + V_C * polyC (evalUBivLK5 gtK.qX_1_sc) = 321489 * (QX_dot / u_of U_C)) ∧
    (polyC (evalUBivLK5 gtK.qY_0_321489) - 9 * (321489 / 63 : A_C) * polyC (evalUBivLK5 gtK.DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 * V_C =
      321489 * (QY_dot / v_of V_C)) ∧
    ((M_mid_int : A_C) * q1_dot =
      ιC_K5 k5Params.Cv0 * U_C * polyC (evalUBivLK5 gtK.q1_0_div_sc) +
      (1 / 243 : A_C) * polyC (evalUBivLK5 gtK.q1_1_sc) * V_C +
      ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 gtK.q1_2_div_sc) * V_C ^ 2) ∧
    ((evalUBivLK5 gtK.qX_0_sc).eval 0 = 0 ∧
     (evalUBivLK5 gtK.qY_0_321489).eval 0 = 0 ∧
     (evalUBivLK5 gtK.q1_0_div_sc).eval 0 = 0 ∧
     (evalUBivLK5 gtK.q1_1_sc).eval 0 = 0)

end SymmetricSexticResidual.LocalResidueQ5


