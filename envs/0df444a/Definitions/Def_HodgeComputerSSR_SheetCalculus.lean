-- Prove2me | Definitions.Def_HodgeComputerSSR_SheetCalculus
-- name    : HodgeComputerSSR_SheetCalculus
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:51:52.590567+00:00
-- url     : https://prove2.me/theorems/1a0a5185-7489-4cc2-81e0-06502729d22b
-- title:
--   Horizontal sheet geometry, $4 \times 4$ fiber Jacobian, and `w_horiz` construction
-- statement:
--   Defines the moving horizontal sheet system $E_0, E_1, E_2, E_3$ in $(a, b, U, V)$ over $(S, Q, T)$, the $4 \times 4$ fiber Jacobian $J_{\mathrm{fib}}$, the $(a, b)$-to-$(S, Q)$ Jacobian $M_{ab,SQ}$, the 10-minor weight polynomials $(A_{0U}, A_{0V}, A_Y, A_X)$, the 18-term numerator $P_{18}$, the lifted weighted divergence `resDivW_L` over any finite extension $L / K_5$, and the explicit horizontal sheet vector `w_horiz a b U V : Fin 4 → L`, along with the $G^2$-cancellation identity and nonvanishing of $W_G$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/SheetCalculus.lean#L1-L1453

import Definitions.Def_HodgeComputerFormal_FiniteDiff
import Definitions.Def_HodgeComputerSSR_K5Field
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false


/-! Moving-sheet differential calculus for `symmetric-sextic-residual`.
Over any finite extension `L / K5`, any nondegenerate sheet `(a, b, U, V) ∈ L^4`
solving the four line-incidence equations `E_0 = E_1 = E_2 = E_3 = 0` carries an
explicit 4-component tangent vector `w_horiz(a, b, U, V) ∈ L^4` whose weighted
residue divergence satisfies the exact pointwise identity
  `2 * W2 * H0^2 * resDivW_L (w_horiz a b U V) = -P18_of ... / (81 * det (J_fib ...))`. -/

noncomputable section
namespace SymmetricSexticResidual.SheetCalculus
open SymmetricSexticResidual.K5Field HoldoutConstruction MvPolynomial
open scoped BigOperators Matrix

/-! ### Section 1: Polymorphic Algebraic Functions and Pure-Ring Identities -/

section PolyAlgebra
variable {R : Type*} [Field R] [CharZero R]

def u_of (U : R) : R := (U - 1) / 9
def v_of (V : R) : R := (V - 1) / 9
def u3_of (S Q x : R) : R := x - S + 2 * Q
def v3_of (T y : R) : R := y - T + 2

def H0_of (S Q T : R) : R :=
  -2 * S ^ 3 + 6 * S ^ 2 * Q - 3 * S * Q ^ 2 - 2 * Q ^ 3 -
  2 * T ^ 3 + 6 * T ^ 2 - 3 * T - 2 + (5 / 7) * Q ^ 2 + (10 / 7) * Q

def F5_of (S Q T x y : R) : R :=
  3 * S * x ^ 2 + 3 * T * y ^ 2 + H0_of S Q T

def DX2_of (S Q x : R) : R :=
  let u3 := u3_of S Q x
  S * Q ^ 2 - 4 * Q ^ 3 - 4 * S ^ 2 * u3 - 27 * S * u3 ^ 2 + 18 * S * Q * u3

def DY2_of (T y : R) : R :=
  let v3 := v3_of T y
  T - 4 - 4 * T ^ 2 * v3 - 27 * T * v3 ^ 2 + 18 * T * v3

def W2_of (S Q T x y : R) : R := S * T * DX2_of S Q x * DY2_of T y

def LX_of (S Q x U : R) : R :=
  let u := u_of U
  U * u3_of S Q x + ((3 + 2 * u) * S - (6 + 9 * u) * Q) / 3

def LY_of (T y V : R) : R :=
  let v := v_of V
  V * v3_of T y + ((3 + 2 * v) * T - (6 + 9 * v)) / 3

def G_of (S Q T x y U V : R) : R :=
  u_of U * DX2_of S Q x + v_of V * DY2_of T y

def PQ_of (S Q T x y U V : R) : R :=
  3 * V * S * LX_of S Q x U ^ 2 + 3 * U * T * LY_of T y V ^ 2

def H_cub (S Q T V0 U V : R) : R :=
  -(4 / 243) * (S - 3 * Q) ^ 3 * U ^ 2 * V
  - (4 / 243) * (T - 3 * V0) ^ 3 * U * V ^ 2
  + ((143 / 243) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3
     + (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 * V0 + (52 / 9) * T * V0 ^ 2 - (22 / 9) * V0 ^ 3
     + (5 / 7) * Q ^ 2 * V0 + (10 / 7) * Q * V0 ^ 2) * U * V
  - (25 / 243) * S * (5 * S - 9 * Q) ^ 2 * V
  - (25 / 243) * T * (5 * T - 9 * V0) ^ 2 * U

def A1_of (S Q U V : R) : R :=
  (1 / 27) * V * (25 * S * (5 * S - 9 * Q) ^ 2 - 4 * (S - 3 * Q) ^ 3 * U)

def B1_of (T U V : R) : R :=
  (1 / 27) * U * (25 * T * (5 * T - 9) ^ 2 - 4 * (T - 3) ^ 3 * V)

lemma H_cub_eq_F5_G_PQ (S Q T x y U V : R) :
    H_cub S Q T 1 U V = U * V * (F5_of S Q T x y - G_of S Q T x y U V) - PQ_of S Q T x y U V := by
  simp only [H_cub, F5_of, H0_of, G_of, PQ_of, DX2_of, DY2_of, LX_of, LY_of, u3_of, v3_of, u_of, v_of]
  ring

lemma H_cub_eq_H0_A1_B1 (S Q T U V : R) :
    H_cub S Q T 1 U V = U * V * H0_of S Q T + u_of U * A1_of S Q U V + v_of V * B1_of T U V := by
  simp only [H_cub, H0_of, A1_of, B1_of, u_of, v_of]
  ring

-- Partial derivatives of H_cub wrt S, Q, T, U, V (at fixed V0)
def dH_dS (S Q U V : R) : R :=
  -(4 / 81) * (S - 3 * Q) ^ 2 * U ^ 2 * V
  + ((143 / 81) * S ^ 2 - (184 / 27) * S * Q + (52 / 9) * Q ^ 2) * U * V
  - (25 / 243) * (5 * S - 9 * Q) * (15 * S - 9 * Q) * V

def dH_dQ (S Q V0 U V : R) : R :=
  (4 / 27) * (S - 3 * Q) ^ 2 * U ^ 2 * V
  + (-(92 / 27) * S ^ 2 + (104 / 9) * S * Q - (22 / 3) * Q ^ 2
     + (10 / 7) * Q * V0 + (10 / 7) * V0 ^ 2) * U * V
  + (50 / 27) * S * (5 * S - 9 * Q) * V

def dH_dT (T V0 U V : R) : R :=
  -(4 / 81) * (T - 3 * V0) ^ 2 * U * V ^ 2
  + ((143 / 81) * T ^ 2 - (184 / 27) * T * V0 + (52 / 9) * V0 ^ 2) * U * V
  - (25 / 243) * (5 * T - 9 * V0) * (15 * T - 9 * V0) * U

def dH_dU (S Q T V0 U V : R) : R :=
  -(8 / 243) * (S - 3 * Q) ^ 3 * U * V
  - (4 / 243) * (T - 3 * V0) ^ 3 * V ^ 2
  + ((143 / 243) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3
     + (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 * V0 + (52 / 9) * T * V0 ^ 2 - (22 / 9) * V0 ^ 3
     + (5 / 7) * Q ^ 2 * V0 + (10 / 7) * Q * V0 ^ 2) * V
  - (25 / 243) * T * (5 * T - 9 * V0) ^ 2

def dH_dV (S Q T V0 U V : R) : R :=
  -(4 / 243) * (S - 3 * Q) ^ 3 * U ^ 2
  - (8 / 243) * (T - 3 * V0) ^ 3 * U * V
  + ((143 / 243) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3
     + (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 * V0 + (52 / 9) * T * V0 ^ 2 - (22 / 9) * V0 ^ 3
     + (5 / 7) * Q ^ 2 * V0 + (10 / 7) * Q * V0 ^ 2) * U
  - (25 / 243) * S * (5 * S - 9 * Q) ^ 2

-- The four line-incidence equations E_0, E_1, E_2, E_3 defined via polarization of H_cub!
def E_fn (k : Fin 4) (S Q T a b U V : R) : R :=
  match k with
  | 0 => H_cub S Q T 1 U V
  | 1 => (H_cub (S + a) (Q + b) (T + 1) 1 U V - H_cub (S - a) (Q - b) (T - 1) 1 U V) / 2 - H_cub a b 1 0 U V
  | 2 => (H_cub (S + a) (Q + b) (T + 1) 1 U V + H_cub (S - a) (Q - b) (T - 1) 1 U V) / 2 - H_cub S Q T 1 U V
  | 3 => H_cub a b 1 0 U V

lemma H_cub_taylor (S Q T a b U V t : R) :
    H_cub (S + a * t) (Q + b * t) (T + t) 1 U V =
      E_fn 0 S Q T a b U V + E_fn 1 S Q T a b U V * t +
      E_fn 2 S Q T a b U V * t ^ 2 + E_fn 3 S Q T a b U V * t ^ 3 := by
  simp only [E_fn, H_cub]; ring

-- Exact partial derivatives of E_fn via polarization of dH_d*!
def dE_dS (k : Fin 4) (S Q _T a b U V : R) : R :=
  match k with
  | 0 => dH_dS S Q U V
  | 1 => (dH_dS (S + a) (Q + b) U V - dH_dS (S - a) (Q - b) U V) / 2
  | 2 => (dH_dS (S + a) (Q + b) U V + dH_dS (S - a) (Q - b) U V) / 2 - dH_dS S Q U V
  | 3 => 0

def dE_dQ (k : Fin 4) (S Q _T a b U V : R) : R :=
  match k with
  | 0 => dH_dQ S Q 1 U V
  | 1 => (dH_dQ (S + a) (Q + b) 1 U V - dH_dQ (S - a) (Q - b) 1 U V) / 2
  | 2 => (dH_dQ (S + a) (Q + b) 1 U V + dH_dQ (S - a) (Q - b) 1 U V) / 2 - dH_dQ S Q 1 U V
  | 3 => 0

def dE_dT (k : Fin 4) (_S _Q T _a _b U V : R) : R :=
  match k with
  | 0 => dH_dT T 1 U V
  | 1 => (dH_dT (T + 1) 1 U V - dH_dT (T - 1) 1 U V) / 2
  | 2 => (dH_dT (T + 1) 1 U V + dH_dT (T - 1) 1 U V) / 2 - dH_dT T 1 U V
  | 3 => 0

def dE_da (k : Fin 4) (S Q _T a b U V : R) : R :=
  match k with
  | 0 => 0
  | 1 => (dH_dS (S + a) (Q + b) U V + dH_dS (S - a) (Q - b) U V) / 2 - dH_dS a b U V
  | 2 => (dH_dS (S + a) (Q + b) U V - dH_dS (S - a) (Q - b) U V) / 2
  | 3 => dH_dS a b U V

def dE_db (k : Fin 4) (S Q _T a b U V : R) : R :=
  match k with
  | 0 => 0
  | 1 => (dH_dQ (S + a) (Q + b) 1 U V + dH_dQ (S - a) (Q - b) 1 U V) / 2 - dH_dQ a b 0 U V
  | 2 => (dH_dQ (S + a) (Q + b) 1 U V - dH_dQ (S - a) (Q - b) 1 U V) / 2
  | 3 => dH_dQ a b 0 U V

def dE_dU (k : Fin 4) (S Q T a b U V : R) : R :=
  match k with
  | 0 => dH_dU S Q T 1 U V
  | 1 => (dH_dU (S + a) (Q + b) (T + 1) 1 U V - dH_dU (S - a) (Q - b) (T - 1) 1 U V) / 2 - dH_dU a b 1 0 U V
  | 2 => (dH_dU (S + a) (Q + b) (T + 1) 1 U V + dH_dU (S - a) (Q - b) (T - 1) 1 U V) / 2 - dH_dU S Q T 1 U V
  | 3 => dH_dU a b 1 0 U V

def dE_dV (k : Fin 4) (S Q T a b U V : R) : R :=
  match k with
  | 0 => dH_dV S Q T 1 U V
  | 1 => (dH_dV (S + a) (Q + b) (T + 1) 1 U V - dH_dV (S - a) (Q - b) (T - 1) 1 U V) / 2 - dH_dV a b 1 0 U V
  | 2 => (dH_dV (S + a) (Q + b) (T + 1) 1 U V + dH_dV (S - a) (Q - b) (T - 1) 1 U V) / 2 - dH_dV S Q T 1 U V
  | 3 => dH_dV a b 1 0 U V

lemma line_shift_E (k : Fin 4) (S Q T a b U V : R) :
    a * dE_dS k S Q T a b U V + b * dE_dQ k S Q T a b U V + dE_dT k S Q T a b U V =
      match k with
      | 0 => E_fn 1 S Q T a b U V
      | 1 => 2 * E_fn 2 S Q T a b U V
      | 2 => 3 * E_fn 3 S Q T a b U V
      | 3 => 0 := by
  fin_cases k <;> simp only [dE_dS, dE_dQ, dE_dT, E_fn, dH_dS, dH_dQ, dH_dT, H_cub] <;> ring

-- 4×4 Fiber Jacobian J_fib and Base-Fiber Matrix M_abSQ
def J_fib (S Q T a b U V : R) : Matrix (Fin 4) (Fin 4) R :=
  fun k j => match j with
    | 0 => dE_da k S Q T a b U V
    | 1 => dE_db k S Q T a b U V
    | 2 => dE_dU k S Q T a b U V
    | 3 => dE_dV k S Q T a b U V

def M_abSQ (S Q T a b U V : R) : Matrix (Fin 4) (Fin 4) R :=
  fun k j => match j with
    | 0 => dE_da k S Q T a b U V
    | 1 => dE_db k S Q T a b U V
    | 2 => dE_dS k S Q T a b U V
    | 3 => dE_dQ k S Q T a b U V

-- Quadratic coefficients of q1 = dH/dsP and q2 = dH/dqP along the line (a*t + ξS*v, b*t + ξQ*v, t, v)
def q1_a2 (a b U V : R) : R := dH_dS a b U V
def q1_a0 (ξS ξQ U V : R) : R := dH_dS ξS ξQ U V
def q1_a1 (a b ξS ξQ U V : R) : R := dH_dS (a + ξS) (b + ξQ) U V - dH_dS a b U V - dH_dS ξS ξQ U V

def q2_b2 (a b U V : R) : R := dH_dQ a b 0 U V
def q2_b0 (ξS ξQ U V : R) : R := dH_dQ ξS ξQ 1 U V
def q2_b1 (a b ξS ξQ U V : R) : R :=
  (dH_dQ (a + ξS) (b + ξQ) 0 U V - dH_dQ a b 0 U V - dH_dQ ξS ξQ 0 U V) + (10 / 7) * b * U * V

def S_ab_mat (a b ξS ξQ U V : R) : Matrix (Fin 4) (Fin 4) R :=
  ![![0, 0, q1_a0 ξS ξQ U V, q2_b0 ξS ξQ U V],
    ![q1_a0 ξS ξQ U V, q2_b0 ξS ξQ U V, q1_a1 a b ξS ξQ U V, q2_b1 a b ξS ξQ U V],
    ![q1_a1 a b ξS ξQ U V, q2_b1 a b ξS ξQ U V, q1_a2 a b U V, q2_b2 a b U V],
    ![q1_a2 a b U V, q2_b2 a b U V, 0, 0]]

private def P_shift (T : R) : Matrix (Fin 4) (Fin 4) R :=
  ![![1, T, T ^ 2, T ^ 3],
    ![0, 1, 2 * T, 3 * T ^ 2],
    ![0, 0, 1, 3 * T],
    ![0, 0, 0, 1]]

private def C_right (T : R) : Matrix (Fin 4) (Fin 4) R :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![-T, 0, 1, 0],
    ![0, -T, 0, 1]]

lemma M_abSQ_eq_factor (S Q T a b U V : R) :
    M_abSQ S Q T a b U V = P_shift T * S_ab_mat a b (S - a * T) (Q - b * T) U V * C_right T := by
  let a2 := q1_a2 a b U V; let a1 := q1_a1 a b (S - a * T) (Q - b * T) U V; let a0 := q1_a0 (S - a * T) (Q - b * T) U V
  let b2 := q2_b2 a b U V; let b1 := q2_b1 a b (S - a * T) (Q - b * T) U V; let b0 := q2_b0 (S - a * T) (Q - b * T) U V
  have hS0 : dE_dS 0 S Q T a b U V = a0 + a1 * T + a2 * T ^ 2 := by
    simp only [dE_dS, a2, a1, a0, q1_a2, q1_a1, q1_a0, dH_dS]; ring
  have hS1 : dE_dS 1 S Q T a b U V = a1 + 2 * a2 * T := by
    simp only [dE_dS, a2, a1, q1_a2, q1_a1, dH_dS]; ring
  have hS2 : dE_dS 2 S Q T a b U V = a2 := by
    simp only [dE_dS, a2, q1_a2, dH_dS]; ring
  have hS3 : dE_dS 3 S Q T a b U V = 0 := rfl
  have hQ0 : dE_dQ 0 S Q T a b U V = b0 + b1 * T + b2 * T ^ 2 := by
    simp only [dE_dQ, b2, b1, b0, q2_b2, q2_b1, q2_b0, dH_dQ]; ring
  have hQ1 : dE_dQ 1 S Q T a b U V = b1 + 2 * b2 * T := by
    simp only [dE_dQ, b2, b1, q2_b2, q2_b1, dH_dQ]; ring
  have hQ2 : dE_dQ 2 S Q T a b U V = b2 := by
    simp only [dE_dQ, b2, q2_b2, dH_dQ]; ring
  have hQ3 : dE_dQ 3 S Q T a b U V = 0 := rfl
  have ha0 : dE_da 0 S Q T a b U V = 0 := rfl
  have ha1 : dE_da 1 S Q T a b U V = dE_dS 0 S Q T a b U V := by
    simp only [dE_da, dE_dS, dH_dS]; ring
  have ha2 : dE_da 2 S Q T a b U V = dE_dS 1 S Q T a b U V := by
    simp only [dE_da, dE_dS, dH_dS]
  have ha3 : dE_da 3 S Q T a b U V = dE_dS 2 S Q T a b U V := by
    simp only [dE_da, dE_dS, dH_dS]; ring
  have hb0 : dE_db 0 S Q T a b U V = 0 := rfl
  have hb1 : dE_db 1 S Q T a b U V = dE_dQ 0 S Q T a b U V := by
    simp only [dE_db, dE_dQ, dH_dQ]; ring
  have hb2 : dE_db 2 S Q T a b U V = dE_dQ 1 S Q T a b U V := by
    simp only [dE_db, dE_dQ, dH_dQ]
  have hb3 : dE_db 3 S Q T a b U V = dE_dQ 2 S Q T a b U V := by
    simp only [dE_db, dE_dQ, dH_dQ]; ring
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  simp_rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
       M_abSQ, P_shift, S_ab_mat, C_right,
       Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
       ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hS0, hS1, hS2, hS3, hQ0, hQ1, hQ2, hQ3];
     ring)

lemma M_abSQ_det (S Q T a b U V : R) :
    (M_abSQ S Q T a b U V).det = (S_ab_mat a b (S - a * T) (Q - b * T) U V).det := by
  rw [M_abSQ_eq_factor, Matrix.det_mul, Matrix.det_mul]
  have hP : (P_shift T).det = 1 := by
    have hu : (P_shift T).IsUpperTriangular := by
      intro i j hij; fin_cases i <;> fin_cases j <;>
        first | exact absurd hij (by decide) | rfl
    rw [Matrix.det_of_isUpperTriangular hu, Fin.prod_univ_four]; simp [P_shift]
  have hC : (C_right T).det = 1 := by
    have hl : (C_right T).IsLowerTriangular := by
      intro i j hij; fin_cases i <;> fin_cases j <;>
        first | exact absurd hij (by decide) | rfl
    rw [Matrix.det_of_isLowerTriangular _ hl, Fin.prod_univ_four]; simp [C_right]
  rw [hP, hC, one_mul, mul_one]

-- The 10 quadratic line-section numerators and 18-term horizontal weights (purely in (a, b, ξS, ξQ, U, V)!)
def numM (mi : Fin 10) (a b ξS ξQ U V : R) : R :=
  let a2 := q1_a2 a b U V; let a1 := q1_a1 a b ξS ξQ U V; let a0 := q1_a0 ξS ξQ U V
  let b2 := q2_b2 a b U V; let b1 := q2_b1 a b ξS ξQ U V; let b0 := q2_b0 ξS ξQ U V
  let d20 := a2 * b0 - a0 * b2
  let d21 := a2 * b1 - a1 * b2
  let d10 := a1 * b0 - a0 * b1
  let (m2, m1, m0) : R × R × R := match mi with
    | 0 => (a ^ 2, 2 * a * ξS, ξS ^ 2)
    | 1 => (a * b, a * ξQ + b * ξS, ξS * ξQ)
    | 2 => (b ^ 2, 2 * b * ξQ, ξQ ^ 2)
    | 3 => (a, ξS, 0)
    | 4 => (0, a, ξS)
    | 5 => (b, ξQ, 0)
    | 6 => (0, b, ξQ)
    | 7 => (1, 0, 0)
    | 8 => (0, 1, 0)
    | 9 => (0, 0, 1)
  (1 / 16) * (m2 * d10 - m1 * d20 + m0 * d21)

def A_0U (a b ξS ξQ U V : R) : R :=
  let m := fun i => numM i a b ξS ξQ U V;
  -(19708 / 1257375) * (5 * m 0 - 9 * m 1)
  + (1472 / 1257375) * (5 * m 1 - 9 * m 2)
  - (16 / 729) * (5 * m 3 - 9 * m 5)
  + (188 / 2025) * (5 * m 4 - 9 * m 6)

def A_0V (a b ξS ξQ U V : R) : R :=
  let m := fun i => numM i a b ξS ξQ U V;
  -(892 / 3645) * (5 * m 3 - 9 * m 4)
  + (40 / 81) * (5 * m 5 - 9 * m 6)
  - (112 / 2395) * (5 * m 7 - 9 * m 8)
  + (392 / 11975) * (5 * m 8 - 9 * m 9)

def A_Y (a b ξS ξQ U V : R) : R :=
  let m := fun i => numM i a b ξS ξQ U V;
  -(100 / 243) * (25 * m 3 - 45 * m 4 - 45 * m 5 + 81 * m 6)
  + V * (-(907876 / 33949125) * (5 * m 0 - 9 * m 1)
         + (2258324 / 33949125) * (5 * m 1 - 9 * m 2)
         + (8 / 243) * (5 * m 3 - 9 * m 5)
         - (64 / 675) * (5 * m 4 - 9 * m 6))
  + U * V * (-(123236 / 24249375) * (m 0 + (2790 / 77) * m 6 + 28 * m 8 - (5904 / 77) * m 9)
             + (492944 / 33949125) * (m 1 + (927 / 77) * m 6 + (49 / 5) * m 8 - (21159 / 770) * m 9))

def A_X (a b ξS ξQ U V : R) : R :=
  let m := fun i => numM i a b ξS ξQ U V;
  U * (-(8 / 405) * (5 * m 3 - 9 * m 4)
       - (476 / 7185) * (5 * m 7 - 9 * m 8)
       + (6916 / 35925) * (5 * m 8 - 9 * m 9))

/-! ### Section 2: 1-Forms, Exact Decomposable 2-Form `om`, and 10-Line `G^2` Cancellation -/

-- Explicit partial derivatives wrt (S, Q, T, x, y) = Fin 5 (at fixed U, V)
def dH0_fn (k : Fin 3) (S Q T : R) : R :=
  match k with
  | 0 => -6 * S ^ 2 + 12 * S * Q - 3 * Q ^ 2
  | 1 => 6 * S ^ 2 - 6 * S * Q - 6 * Q ^ 2 + (10 / 7) * Q + 10 / 7
  | 2 => -6 * T ^ 2 + 12 * T - 3

def dF5_fn (k : Fin 5) (S Q T x y : R) : R :=
  match k with
  | 0 => 3 * x ^ 2 + dH0_fn 0 S Q T
  | 1 => dH0_fn 1 S Q T
  | 2 => 3 * y ^ 2 + dH0_fn 2 S Q T
  | 3 => 6 * S * x
  | 4 => 6 * T * y

def dDX2_fn (k : Fin 5) (S Q x : R) : R :=
  let u3 := u3_of S Q x
  match k with
  | 0 => Q ^ 2 - 8 * S * u3 + 4 * S ^ 2 - 27 * u3 ^ 2 + 54 * S * u3 + 18 * Q * u3 - 18 * S * Q
  | 1 => 2 * S * Q - 12 * Q ^ 2 - 8 * S ^ 2 - 108 * S * u3 + 18 * S * u3 + 36 * S * Q
  | 2 => 0
  | 3 => -4 * S ^ 2 - 54 * S * u3 + 18 * S * Q
  | 4 => 0

def dDY2_fn (k : Fin 5) (T y : R) : R :=
  let v3 := v3_of T y
  match k with
  | 0 => 0
  | 1 => 0
  | 2 => 1 - 8 * T * v3 + 4 * T ^ 2 - 27 * v3 ^ 2 + 54 * T * v3 + 18 * v3 - 18 * T
  | 3 => 0
  | 4 => -4 * T ^ 2 - 54 * T * v3 + 18 * T

def dG_fn (k : Fin 5) (S Q T x y U V : R) : R :=
  u_of U * dDX2_fn k S Q x + v_of V * dDY2_fn k T y

def dW2_fn (k : Fin 5) (S Q T x y : R) : R :=
  let dX := DX2_of S Q x; let dY := DY2_of T y
  let dS : R := match k with | 0 => 1 | _ => 0
  let dT : R := match k with | 2 => 1 | _ => 0
  dS * T * dX * dY + S * dT * dX * dY + S * T * dDX2_fn k S Q x * dY + S * T * dX * dDY2_fn k T y

def dLX_fn (k : Fin 5) (U : R) : R :=
  let u := u_of U
  match k with
  | 0 => -U + (3 + 2 * u) / 3
  | 1 => 2 * U - (6 + 9 * u) / 3
  | 2 => 0
  | 3 => U
  | 4 => 0

def dLY_fn (k : Fin 5) (V : R) : R :=
  let v := v_of V
  match k with
  | 0 => 0
  | 1 => 0
  | 2 => -V + (3 + 2 * v) / 3
  | 3 => 0
  | 4 => V

def dPQ_fn (k : Fin 5) (S Q T x y U V : R) : R :=
  let lx := LX_of S Q x U; let ly := LY_of T y V
  let dS : R := match k with | 0 => 1 | _ => 0
  let dT : R := match k with | 2 => 1 | _ => 0
  3 * V * dS * lx ^ 2 + 6 * V * S * lx * dLX_fn k U +
  3 * U * dT * ly ^ 2 + 6 * U * T * ly * dLY_fn k V

def dA1_fn (k : Fin 3) (S Q U V : R) : R :=
  match k with
  | 0 => (1 / 27) * V * (25 * (5 * S - 9 * Q) * (15 * S - 9 * Q) - 12 * (S - 3 * Q) ^ 2 * U)
  | 1 => (1 / 27) * V * (-450 * S * (5 * S - 9 * Q) + 36 * (S - 3 * Q) ^ 2 * U)
  | 2 => 0

def br_fn (k : Fin 5) (S Q T x y U V : R) : R :=
  let lx := LX_of S Q x U; let ly := LY_of T y V
  let base : R := match k with | 0 => -T * lx * ly | 2 => S * lx * ly | _ => 0
  base + 2 * S * T * (lx * dLY_fn k V - ly * dLX_fn k U)

def dbr_fn (k j : Fin 5) (S Q T x y U V : R) : R :=
  -- ∂(br_fn k) / ∂z_j (at fixed U, V)
  let lx := LX_of S Q x U; let ly := LY_of T y V
  let dlxj := dLX_fn j U; let dlyj := dLY_fn j V
  let dS : R := match j with | 0 => 1 | _ => 0
  let dT : R := match j with | 2 => 1 | _ => 0
  let dbase : R := match k with
    | 0 => -(dT * lx * ly + T * dlxj * ly + T * lx * dlyj)
    | 2 => dS * lx * ly + S * dlxj * ly + S * lx * dlyj
    | _ => 0
  dbase + 2 * (dS * T + S * dT) * (lx * dLY_fn k V - ly * dLX_fn k U) +
    2 * S * T * (dlxj * dLY_fn k V - dlyj * dLX_fn k U)

def PhiY_fn (k : Fin 5) (S Q T x y U V : R) : R :=
  DY2_of T y * br_fn k S Q T x y U V

def dPhiY_fn (k j : Fin 5) (S Q T x y U V : R) : R :=
  dDY2_fn j T y * br_fn k S Q T x y U V + DY2_of T y * dbr_fn k j S Q T x y U V

def PhiX_fn (k : Fin 5) (S Q T x y U V : R) : R :=
  -DX2_of S Q x * br_fn k S Q T x y U V

def dPhiX_fn (k j : Fin 5) (S Q T x y U V : R) : R :=
  -dDX2_fn j S Q x * br_fn k S Q T x y U V - DX2_of S Q x * dbr_fn k j S Q T x y U V

-- Exact decomposable 2-form `om` satisfying `dPQ ∧ br = PQ * om` and `curl_ST(br) = 2*S*T*om`
def om_fn (i j : Fin 5) (S Q T x y U V : R) : R :=
  let aX := -25 * S * U + 15 * Q * U + 9 * x * U + 25 * S - 15 * Q
  let aY := -25 * T * V + 9 * y * V + 25 * T + 15 * V - 15
  let omX : Fin 5 → R := fun k => match k with | 0 => aX | 1 => 30 * (U - 1) * S | 3 => 18 * U * S | _ => 0
  let omY : Fin 5 → R := fun k => match k with | 2 => aY | 4 => 18 * V * T | _ => 0
  (1 / 81) * (omX i * omY j - omX j * omY i)

lemma dPQ_wedge_br (i j : Fin 5) (S Q T x y U V : R) :
    dPQ_fn i S Q T x y U V * br_fn j S Q T x y U V -
    dPQ_fn j S Q T x y U V * br_fn i S Q T x y U V =
      PQ_of S Q T x y U V * om_fn i j S Q T x y U V := by
  fin_cases i <;> fin_cases j <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
       dPQ_fn, br_fn, PQ_of, om_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of];
     ring)

def curl_num_fn (Phi : Fin 5 → R) (dPhi : Fin 5 → Fin 5 → R) (S Q T x y U V : R) (i j : Fin 5) : R :=
  let W2 := W2_of S Q T x y
  let G := G_of S Q T x y U V
  2 * W2 * G * (dPhi j i - dPhi i j)
  - G * (Phi j * dW2_fn i S Q T x y - Phi i * dW2_fn j S Q T x y)
  - 2 * W2 * (Phi j * dG_fn i S Q T x y U V - Phi i * dG_fn j S Q T x y U V)

private def dST_fn (k : Fin 5) (S T : R) : R :=
  (match k with | 0 => 1 | _ => 0) * T + S * (match k with | 2 => 1 | _ => 0)

private lemma curl_ST_br (i j : Fin 5) (S Q T x y U V : R) :
    2 * S * T * (dbr_fn j i S Q T x y U V - dbr_fn i j S Q T x y U V) -
    (br_fn j S Q T x y U V * dST_fn i S T - br_fn i S Q T x y U V * dST_fn j S T) =
      2 * S * T * om_fn i j S Q T x y U V := by
  fin_cases i <;> fin_cases j <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
       br_fn, dbr_fn, dST_fn, om_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of];
     ring)

lemma v_curl_PhiY_eq (i j : Fin 5) (S Q T x y U V : R) :
    v_of V * curl_num_fn (fun k => PhiY_fn k S Q T x y U V)
      (fun k l => dPhiY_fn k l S Q T x y U V) S Q T x y U V i j =
      2 * v_of V * S * T * DX2_of S Q x * DY2_of T y ^ 2 *
        (G_of S Q T x y U V * om_fn i j S Q T x y U V -
          (dG_fn i S Q T x y U V * br_fn j S Q T x y U V - dG_fn j S Q T x y U V * br_fn i S Q T x y U V))
      + G_of S Q T x y U V * S * T * DX2_of S Q x * DY2_of T y *
        (dG_fn i S Q T x y U V * br_fn j S Q T x y U V - dG_fn j S Q T x y U V * br_fn i S Q T x y U V)
      - G_of S Q T x y U V ^ 2 * S * T * DY2_of T y *
        (dDX2_fn i S Q x * br_fn j S Q T x y U V - dDX2_fn j S Q x * br_fn i S Q T x y U V) := by
  have hbr := curl_ST_br i j S Q T x y U V
  simp only [curl_num_fn, PhiY_fn, dPhiY_fn, W2_of, dW2_fn, G_of, dG_fn]
  dsimp only [dST_fn] at hbr
  linear_combination v_of V * (u_of U * DX2_of S Q x + v_of V * DY2_of T y) * DX2_of S Q x * DY2_of T y ^ 2 * hbr

lemma u_curl_PhiX_eq (i j : Fin 5) (S Q T x y U V : R) :
    u_of U * curl_num_fn (fun k => PhiX_fn k S Q T x y U V)
      (fun k l => dPhiX_fn k l S Q T x y U V) S Q T x y U V i j =
      -2 * u_of U * S * T * DX2_of S Q x ^ 2 * DY2_of T y *
        (G_of S Q T x y U V * om_fn i j S Q T x y U V -
          (dG_fn i S Q T x y U V * br_fn j S Q T x y U V - dG_fn j S Q T x y U V * br_fn i S Q T x y U V))
      - G_of S Q T x y U V * S * T * DX2_of S Q x * DY2_of T y *
        (dG_fn i S Q T x y U V * br_fn j S Q T x y U V - dG_fn j S Q T x y U V * br_fn i S Q T x y U V)
      + G_of S Q T x y U V ^ 2 * S * T * DX2_of S Q x *
        (dDY2_fn i T y * br_fn j S Q T x y U V - dDY2_fn j T y * br_fn i S Q T x y U V) := by
  have hbr := curl_ST_br i j S Q T x y U V
  simp only [curl_num_fn, PhiX_fn, dPhiX_fn, W2_of, dW2_fn, G_of, dG_fn]
  dsimp only [dST_fn] at hbr
  linear_combination -u_of U * (u_of U * DX2_of S Q x + v_of V * DY2_of T y) * DX2_of S Q x ^ 2 * DY2_of T y * hbr

-- Contraction of a 2-form with dF_5 along (a, b, 1)
def F_contract (S Q T x y : R) (f2 : Fin 5 → Fin 5 → R) (i : Fin 3) : R :=
  let idx : Fin 5 := match i with | 0 => 0 | 1 => 1 | 2 => 2
  dF5_fn 4 S Q T x y * f2 idx 3 +
  dF5_fn 3 S Q T x y * f2 4 idx +
  dF5_fn idx S Q T x y * f2 3 4

def dot_ab (v : Fin 3 → R) (a b : R) : R := v 0 * a + v 1 * b + v 2

def Omega_F (S Q T x y U V : R) (i : Fin 3) : R :=
  F_contract S Q T x y (fun p q => S * T * om_fn p q S Q T x y U V) i

def dDX2_F (S Q T x y U V : R) (i : Fin 3) : R :=
  F_contract S Q T x y (fun p q =>
    S * T * (dDX2_fn p S Q x * br_fn q S Q T x y U V - dDX2_fn q S Q x * br_fn p S Q T x y U V)) i

def dDY2_F (S Q T x y U V : R) (i : Fin 3) : R :=
  F_contract S Q T x y (fun p q =>
    S * T * (dDY2_fn p T y * br_fn q S Q T x y U V - dDY2_fn q T y * br_fn p S Q T x y U V)) i

def QY_num (S Q T x y U V : R) (i : Fin 3) : R :=
  DY2_of T y * (DX2_of S Q x * Omega_F S Q T x y U V i - dDX2_F S Q T x y U V i)

def QX_num (S Q T x y U V : R) (i : Fin 3) : R :=
  DX2_of S Q x * (-DY2_of T y * Omega_F S Q T x y U V i + dDY2_F S Q T x y U V i)

def EB_of (S Q T x y U V : R) : R :=
  2 * W2_of S Q T x y * (dF5_fn 4 S Q T x y * br_fn 3 S Q T x y U V -
    dF5_fn 3 S Q T x y * br_fn 4 S Q T x y U V)

def CY_of (S Q T x y U V : R) (i : Fin 3) : R :=
  F_contract S Q T x y (curl_num_fn (fun k => PhiY_fn k S Q T x y U V)
    (fun k l => dPhiY_fn k l S Q T x y U V) S Q T x y U V) i

def CX_of (S Q T x y U V : R) (i : Fin 3) : R :=
  F_contract S Q T x y (curl_num_fn (fun k => PhiX_fn k S Q T x y U V)
    (fun k l => dPhiX_fn k l S Q T x y U V) S Q T x y U V) i

def cA1_of (S Q T a b U V : R) : R :=
  let H0 := H0_of S Q T; let A1 := A1_of S Q U V
  (H0 * dA1_fn 0 S Q U V - A1 * dH0_fn 0 S Q T) * a +
  (H0 * dA1_fn 1 S Q U V - A1 * dH0_fn 1 S Q T) * b +
  (H0 * dA1_fn 2 S Q U V - A1 * dH0_fn 2 S Q T)

def P18_of (S Q T x y a b U V : R) : R :=
  let ξS := S - a * T; let ξQ := Q - b * T
  let M0 := A_0U a b ξS ξQ U V / U + A_0V a b ξS ξQ U V / V
  let MY := A_Y a b ξS ξQ U V
  let MX := A_X a b ξS ξQ U V
  let H0 := H0_of S Q T
  let qY := dot_ab (QY_num S Q T x y U V) a b / v_of V
  let qX := dot_ab (QX_num S Q T x y U V) a b / u_of U
  let q1 := H0 * A1_of S Q U V * qY + H0 * B1_of T U V * qX +
    (cA1_of S Q T a b U V / v_of V) * EB_of S Q T x y U V
  M0 * q1 + (MY * qY + MX * qX) * H0 ^ 2

-- Helper: gradient identity for H_cub(S, Q, T, 1, U, V) wrt Fin 5 (note ∂H/∂x = ∂H/∂y = 0!)
private def dH_fin5 (k : Fin 5) (S Q T U V : R) : R :=
  match k with
  | 0 => dH_dS S Q U V
  | 1 => dH_dQ S Q 1 U V
  | 2 => dH_dT T 1 U V
  | 3 => 0
  | 4 => 0

private lemma dH_eq_UV_dF5_sub_dG_sub_dPQ (k : Fin 5) (S Q T x y U V : R) :
    dH_fin5 k S Q T U V =
      U * V * (dF5_fn k S Q T x y - dG_fn k S Q T x y U V) - dPQ_fn k S Q T x y U V := by
  fin_cases k <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
       dH_fin5, dH_dS, dH_dQ, dH_dT, dF5_fn, dH0_fn, dG_fn, dDX2_fn, dDY2_fn,
       dPQ_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of];
     ring)

private lemma E1_eq_dot_dH (S Q T a b U V : R) :
    E_fn 1 S Q T a b U V = a * dH_dS S Q U V + b * dH_dQ S Q 1 U V + dH_dT T 1 U V := by
  have h := line_shift_E 0 S Q T a b U V
  simpa only [dE_dS, dE_dQ, dE_dT] using h.symm

lemma G_sq_cancellation (S Q T x y a b U V : R)
    (hF : F5_of S Q T x y = 0)
    (hE0 : E_fn 0 S Q T a b U V = 0)
    (hE1 : E_fn 1 S Q T a b U V = 0)
    (hU : U ≠ 0) (hV : V ≠ 0) :
    v_of V * dot_ab (CY_of S Q T x y U V) a b =
      G_of S Q T x y U V ^ 2 * dot_ab (QY_num S Q T x y U V) a b ∧
    u_of U * dot_ab (CX_of S Q T x y U V) a b =
      G_of S Q T x y U V ^ 2 * dot_ab (QX_num S Q T x y U V) a b := by
  let br := fun k => br_fn k S Q T x y U V
  let dG_F : Fin 3 → R := fun i =>
    F_contract S Q T x y (fun p q => S * T * (dG_fn p S Q T x y U V * br q - dG_fn q S Q T x y U V * br p)) i
  -- Step 1: On F5=0, E0=0, E1=0, prove dot_ab dG_F a b = G * dot_ab Omega_F a b!
  have hPQ : PQ_of S Q T x y U V = -(U * V * G_of S Q T x y U V) := by
    have h0 := H_cub_eq_F5_G_PQ S Q T x y U V
    change E_fn 0 S Q T a b U V = _ at h0
    rw [hE0, hF] at h0; linear_combination h0
  have hdG_eq : dot_ab dG_F a b = G_of S Q T x y U V * dot_ab (Omega_F S Q T x y U V) a b := by
    have hpair_H : dot_ab (fun i => F_contract S Q T x y
        (fun p q => dH_fin5 p S Q T U V * br q - dH_fin5 q S Q T U V * br p) i) a b = 0 := by
      have he1 := E1_eq_dot_dH S Q T a b U V
      rw [hE1] at he1
      simp only [dot_ab, F_contract, dH_fin5]
      linear_combination (dF5_fn 3 S Q T x y * br 4 - dF5_fn 4 S Q T x y * br 3) * he1
    have hpair_F : dot_ab (fun i => F_contract S Q T x y
        (fun p q => dF5_fn p S Q T x y * br q - dF5_fn q S Q T x y * br p) i) a b = 0 := by
      simp only [dot_ab, F_contract]; ring
    have hlin : dot_ab (fun i => F_contract S Q T x y
        (fun p q => dH_fin5 p S Q T U V * br q - dH_fin5 q S Q T U V * br p) i) a b =
        U * V * dot_ab (fun i => F_contract S Q T x y
          (fun p q => dF5_fn p S Q T x y * br q - dF5_fn q S Q T x y * br p) i) a b -
        U * V * dot_ab (fun i => F_contract S Q T x y
          (fun p q => dG_fn p S Q T x y U V * br q - dG_fn q S Q T x y U V * br p) i) a b -
        PQ_of S Q T x y U V * dot_ab (fun i => F_contract S Q T x y
          (fun p q => om_fn p q S Q T x y U V) i) a b := by
      have h2form (p q : Fin 5) :
          dH_fin5 p S Q T U V * br q - dH_fin5 q S Q T U V * br p =
            U * V * (dF5_fn p S Q T x y * br q - dF5_fn q S Q T x y * br p) -
            U * V * (dG_fn p S Q T x y U V * br q - dG_fn q S Q T x y U V * br p) -
            PQ_of S Q T x y U V * om_fn p q S Q T x y U V := by
        dsimp only [br]
        rw [dH_eq_UV_dF5_sub_dG_sub_dPQ p S Q T x y U V,
            dH_eq_UV_dF5_sub_dG_sub_dPQ q S Q T x y U V, ← dPQ_wedge_br]
        ring
      simp only [dot_ab, F_contract, h2form]
      ring
    rw [hpair_H, hpair_F, mul_zero, zero_sub, hPQ] at hlin
    have hcancel : U * V * (dot_ab (fun i => F_contract S Q T x y
        (fun p q => dG_fn p S Q T x y U V * br q - dG_fn q S Q T x y U V * br p) i) a b -
        G_of S Q T x y U V * dot_ab (fun i => F_contract S Q T x y
          (fun p q => om_fn p q S Q T x y U V) i) a b) = 0 := by
      linear_combination hlin
    have hsub0 : dot_ab (fun i => F_contract S Q T x y
        (fun p q => dG_fn p S Q T x y U V * br q - dG_fn q S Q T x y U V * br p) i) a b =
        G_of S Q T x y U V * dot_ab (fun i => F_contract S Q T x y
          (fun p q => om_fn p q S Q T x y U V) i) a b :=
      sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left (mul_ne_zero hU hV))
    have hST : dot_ab dG_F a b = S * T * dot_ab (fun i => F_contract S Q T x y
        (fun p q => dG_fn p S Q T x y U V * br q - dG_fn q S Q T x y U V * br p) i) a b := by
      simp only [dot_ab, dG_F, F_contract]; ring
    have hSTom : dot_ab (Omega_F S Q T x y U V) a b = S * T * dot_ab (fun i => F_contract S Q T x y
        (fun p q => om_fn p q S Q T x y U V) i) a b := by
      simp only [dot_ab, Omega_F, F_contract]; ring
    rw [hST, hSTom, hsub0]; ring
  -- Step 2: Plug into v_curl_PhiY_eq and u_curl_PhiX_eq!
  constructor
  · have hY : v_of V * dot_ab (CY_of S Q T x y U V) a b =
        2 * v_of V * DX2_of S Q x * DY2_of T y ^ 2 *
          (G_of S Q T x y U V * dot_ab (Omega_F S Q T x y U V) a b - dot_ab dG_F a b)
        + G_of S Q T x y U V * DX2_of S Q x * DY2_of T y * dot_ab dG_F a b
        - G_of S Q T x y U V ^ 2 * DY2_of T y * dot_ab (dDX2_F S Q T x y U V) a b := by
      simp only [dot_ab, CY_of, Omega_F, dG_F, dDX2_F, F_contract]
      have h03 := v_curl_PhiY_eq 0 3 S Q T x y U V
      have h40 := v_curl_PhiY_eq 4 0 S Q T x y U V
      have h13 := v_curl_PhiY_eq 1 3 S Q T x y U V
      have h41 := v_curl_PhiY_eq 4 1 S Q T x y U V
      have h23 := v_curl_PhiY_eq 2 3 S Q T x y U V
      have h42 := v_curl_PhiY_eq 4 2 S Q T x y U V
      have h34 := v_curl_PhiY_eq 3 4 S Q T x y U V
      linear_combination
        a * dF5_fn 4 S Q T x y * h03 + a * dF5_fn 3 S Q T x y * h40 + a * dF5_fn 0 S Q T x y * h34 +
        b * dF5_fn 4 S Q T x y * h13 + b * dF5_fn 3 S Q T x y * h41 + b * dF5_fn 1 S Q T x y * h34 +
        dF5_fn 4 S Q T x y * h23 + dF5_fn 3 S Q T x y * h42 + dF5_fn 2 S Q T x y * h34
    rw [hY, hdG_eq]
    simp only [dot_ab, QY_num]; ring
  · have hX : u_of U * dot_ab (CX_of S Q T x y U V) a b =
        -2 * u_of U * DX2_of S Q x ^ 2 * DY2_of T y *
          (G_of S Q T x y U V * dot_ab (Omega_F S Q T x y U V) a b - dot_ab dG_F a b)
        - G_of S Q T x y U V * DX2_of S Q x * DY2_of T y * dot_ab dG_F a b
        + G_of S Q T x y U V ^ 2 * DX2_of S Q x * dot_ab (dDY2_F S Q T x y U V) a b := by
      simp only [dot_ab, CX_of, Omega_F, dG_F, dDY2_F, F_contract]
      have h03 := u_curl_PhiX_eq 0 3 S Q T x y U V
      have h40 := u_curl_PhiX_eq 4 0 S Q T x y U V
      have h13 := u_curl_PhiX_eq 1 3 S Q T x y U V
      have h41 := u_curl_PhiX_eq 4 1 S Q T x y U V
      have h23 := u_curl_PhiX_eq 2 3 S Q T x y U V
      have h42 := u_curl_PhiX_eq 4 2 S Q T x y U V
      have h34 := u_curl_PhiX_eq 3 4 S Q T x y U V
      linear_combination
        a * dF5_fn 4 S Q T x y * h03 + a * dF5_fn 3 S Q T x y * h40 + a * dF5_fn 0 S Q T x y * h34 +
        b * dF5_fn 4 S Q T x y * h13 + b * dF5_fn 3 S Q T x y * h41 + b * dF5_fn 1 S Q T x y * h34 +
        dF5_fn 4 S Q T x y * h23 + dF5_fn 3 S Q T x y * h42 + dF5_fn 2 S Q T x y * h34
    rw [hX, hdG_eq]
    simp only [dot_ab, QX_num]; ring

end PolyAlgebra

/-! ### Section 3: Commutativity of Derivations on `K5` and `W_G ≠ 0` -/

section K5Extras
local instance : Algebra ℤ K4 := Ring.toIntAlgebra K4
local instance : Algebra ℤ K5 := Ring.toIntAlgebra K5

private lemma pderiv_poly4_comm (i j : Fin 4) (p : Poly4) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add]
    have hc (a b : Fin 4) : pderiv a ((Pi.single b (1 : Poly4) : Fin 4 → Poly4) k) = 0 := by
      by_cases h : k = b
      · subst h; simp
      · simp [Pi.single_eq_of_ne (M := fun _ : Fin 4 => Poly4) h 1]
    rw [hc, hc, hp]; ring

lemma pderiv4_K4_commute (i j : Fin 4) :
    Function.Commute (pderiv4_K4 i) (pderiv4_K4 j) := by
  exact HoldoutConstruction.extendRingDerivation_commute _ _ (pderiv_poly4_comm i j)

lemma δ_commute (i j : Fin 4) : Function.Commute (δ i) (δ j) :=
  HoldoutConstruction.extendFiniteDerivation_commute (pderiv4_K4 i) (pderiv4_K4 j)
    (pderiv4_K4_commute i j)

lemma W_G_ne_zero : DX2_K * δ 3 DY2_K - DY2_K * δ 3 DX2_K ≠ 0 := by
  have hS := S_K_ne_zero; have hx := x_K_ne_zero
  intro h0
  have hδDY : δ 3 DY2_K = poly4ToK5 (pderiv 3 DY2_4) := by
    rw [DY2_K, ← poly4ToPoly5_DY2, toK5_poly4, δ_poly4]
  have hδDX : δ 3 DX2_K = -(6 * T_K * y_K / (6 * S_K * x_K)) * toK5 (pderiv 3 DX2_5) := by
    rw [DX2_K, δ_toK5]
    have h4 : pderiv (4 : Fin 5) DX2_5 = 0 := by
      simp [DX2_5, u3_5, pderiv_ofNat, pderiv_X]
    simp only [tanIdx, Matrix.cons_val, h4, map_zero, zero_sub, pderiv_4_F5, Fx_K_eq]
    ring
  have h3Sx : 3 * S_K * (S_K * x_K * (DX2_K * δ 3 DY2_K - DY2_K * δ 3 DX2_K)) = 0 := by
    rw [h0, mul_zero, mul_zero]
  rw [hδDY, hδDX] at h3Sx
  have hmul : 3 * S_K * (S_K * x_K * DX2_K * poly4ToK5 (pderiv 3 DY2_4) +
      T_K * y_K * DY2_K * toK5 (pderiv 3 DX2_5)) = 0 := by
    have hSx : S_K * x_K ≠ 0 := mul_ne_zero hS hx
    field_simp [hS, hx] at h3Sx
    linear_combination h3Sx
  -- Reduce to a_4 + b_4 * x_K using 3 * S_K * x_K^2 = -poly4ToK5 radPoly4!
  let A_dx : Poly4 :=
    X 0 * X 1 ^ 2 - 4 * X 1 ^ 3 + 4 * X 0 ^ 3 - 26 * X 0 ^ 2 * X 1 -
    27 * X 0 * (-X 0 + 2 * X 1) ^ 2 + 36 * X 0 * X 1 ^ 2 + 9 * radPoly4
  let B_dx : Poly4 := 50 * X 0 ^ 2 - 90 * X 0 * X 1
  have hDX_lin : DX2_K = poly4ToK5 A_dx + poly4ToK5 B_dx * x_K := by
    have hsq : -27 * S_K * x_K ^ 2 = 9 * poly4ToK5 radPoly4 := by
      have hrad : poly4ToK5 radPoly4 = 3 * T_K * y_K ^ 2 + poly4ToK5 H0_4 := by
        simp only [radPoly4, map_add, map_mul, map_pow, map_ofNat]; rfl
      rw [hrad]; linear_combination -9 * x_K_sq_relation
    have h1 : DX2_K = S_K * Q_K ^ 2 - 4 * Q_K ^ 3 - 4 * S_K ^ 2 * (x_K - S_K + 2 * Q_K) -
        27 * S_K * (x_K - S_K + 2 * Q_K) ^ 2 + 18 * S_K * Q_K * (x_K - S_K + 2 * Q_K) := by
      simp [DX2_K, DX2_5, u3_5, toK5]
    rw [h1]
    have h2 : poly4ToK5 A_dx + poly4ToK5 B_dx * x_K =
        (S_K * Q_K ^ 2 - 4 * Q_K ^ 3 + 4 * S_K ^ 3 - 26 * S_K ^ 2 * Q_K -
          27 * S_K * (-S_K + 2 * Q_K) ^ 2 + 36 * S_K * Q_K ^ 2 + 9 * poly4ToK5 radPoly4) +
        (50 * S_K ^ 2 - 90 * S_K * Q_K) * x_K := by
      simp only [A_dx, B_dx, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]; rfl
    rw [h2, ← hsq]; ring
  have hDXx_lin : toK5 (pderiv 3 DX2_5) = poly4ToK5 B_dx - 54 * S_K * x_K := by
    have hp : pderiv (3 : Fin 5) DX2_5 = 50 * X 0 ^ 2 - 90 * X 0 * X 1 - 54 * X 0 * X 3 := by
      simp only [DX2_5, u3_5, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
        pderiv_ofNat, pderiv_X, smul_eq_mul, nsmul_eq_mul]
      simp; ring
    rw [hp]
    have hB : poly4ToK5 B_dx = 50 * S_K ^ 2 - 90 * S_K * Q_K := by
      simp only [B_dx, map_sub, map_mul, map_pow, map_ofNat]; rfl
    rw [hB]; simp [toK5]
  have hDY_p4 : DY2_K = poly4ToK5 DY2_4 := by rw [DY2_K, ← poly4ToPoly5_DY2, toK5_poly4]
  have h3Sx2 : 3 * S_K * x_K ^ 2 = -poly4ToK5 radPoly4 := by
    have hrad : poly4ToK5 radPoly4 = 3 * T_K * y_K ^ 2 + poly4ToK5 H0_4 := by
      simp only [radPoly4, map_add, map_mul, map_pow, map_ofNat]; rfl
    rw [hrad]; linear_combination x_K_sq_relation
  let C0 : Poly4 := -X 0 * radPoly4 * B_dx * pderiv 3 DY2_4 + 3 * X 0 * X 2 * X 3 * DY2_4 * B_dx
  let C1 : Poly4 := 3 * X 0 ^ 2 * A_dx * pderiv 3 DY2_4 - 162 * X 0 ^ 2 * X 2 * X 3 * DY2_4
  have hlin : k4ToK5 (algebraMap Poly4 K4 C0) + k4ToK5 (algebraMap Poly4 K4 C1) * x_K = 0 := by
    have hC0 : k4ToK5 (algebraMap Poly4 K4 C0) =
        -S_K * poly4ToK5 radPoly4 * poly4ToK5 B_dx * poly4ToK5 (pderiv 3 DY2_4) +
        3 * S_K * T_K * y_K * poly4ToK5 DY2_4 * poly4ToK5 B_dx := by
      simp only [C0, map_add, map_neg, map_mul, map_ofNat]; rfl
    have hC1 : k4ToK5 (algebraMap Poly4 K4 C1) =
        3 * S_K ^ 2 * poly4ToK5 A_dx * poly4ToK5 (pderiv 3 DY2_4) -
        162 * S_K ^ 2 * T_K * y_K * poly4ToK5 DY2_4 := by
      simp only [C1, map_sub, map_mul, map_pow, map_ofNat]; rfl
    rw [hC0, hC1]
    rw [hDX_lin, hDXx_lin, hDY_p4] at hmul
    linear_combination hmul - S_K * poly4ToK5 B_dx * poly4ToK5 (pderiv 3 DY2_4) * h3Sx2
  have hC0_zero : C0 = 0 := by
    have ha := (k5_linear_indep _ _ hlin).1
    exact (IsFractionRing.injective Poly4 K4) (by simpa using ha)
  have hev := congrArg (MvPolynomial.eval ![1, 0, 2, 0]) hC0_zero
  have hpDY : MvPolynomial.eval ![1, 0, 2, 0] (pderiv 3 DY2_4) = 20 := by
    have hdy3 : pderiv (3 : Fin 4) DY2_4 = -4 * X 2 ^ 2 - 54 * X 2 * (X 3 - X 2 + 2) + 18 * X 2 := by
      simp only [DY2_4, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
        pderiv_ofNat, pderiv_X, smul_eq_mul, nsmul_eq_mul]
      simp; ring
    rw [hdy3]; simp; norm_num
  have hrad_ev : MvPolynomial.eval ![1, 0, 2, 0] radPoly4 = -2 := by
    simp [radPoly4, H0_4, H0_3, poly3ToPoly4, map_ofNat]; norm_num
  have hB_ev : MvPolynomial.eval ![1, 0, 2, 0] B_dx = 50 := by
    simp [B_dx]
  simp only [C0, map_add, map_neg, map_mul, map_ofNat, eval_X, Matrix.cons_val_zero,
    Matrix.cons_val, hrad_ev, hB_ev, hpDY, map_zero] at hev
  norm_num at hev

end K5Extras

/-! ### Section 4: Sheet Divergence Calculus on Any Finite Extension `L / K5` -/

section SheetL
variable {L : Type*} [Field L] [Algebra K5 L] [FiniteDimensional K5 L]

local instance : Algebra ℤ K5 := Ring.toIntAlgebra K5
local instance : Algebra ℤ L := Ring.toIntAlgebra L

instance : CharZero L :=
  charZero_of_injective_ringHom (algebraMap K5 L).injective

abbrev ιL : K5 →+* L := algebraMap K5 L

def δL (i : Fin 4) : Derivation ℤ L L :=
  HoldoutConstruction.extendFiniteDerivation (K := K5) (L := L) (δ i)

lemma δL_apply (i : Fin 4) (z : K5) : δL (L := L) i (ιL z) = ιL (δ i z) :=
  HoldoutConstruction.extendFiniteDerivation_apply (δ i) z

lemma δL_commute (i j : Fin 4) : Function.Commute (δL (L := L) i) (δL (L := L) j) :=
  HoldoutConstruction.extendFiniteDerivation_commute (δ i) (δ j) (δ_commute i j)

-- Generic derivation helpers on L (zero side-condition hypotheses!)
omit [FiniteDimensional K5 L] in
private lemma ofNat_ne_zero_L (n : ℕ) [hn : n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : L) ≠ 0 := by
  change (n : L) ≠ 0
  exact Nat.cast_ne_zero.mpr (by have := hn.prop; omega)

omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_ofNat (D : Derivation ℤ L L) (n : ℕ) [n.AtLeastTwo] :
    D (no_index (OfNat.ofNat n)) = 0 := by
  change D (n : L) = 0; exact D.map_natCast n

omit [Algebra K5 L] [FiniteDimensional K5 L] in
private lemma D_div (D : Derivation ℤ L L) (a b : L) (hb : b ≠ 0) :
    D (a / b) = (b * D a - a * D b) / b ^ 2 := by
  have h := congrArg D (div_mul_cancel₀ a hb)
  rw [D.leibniz] at h; simp only [smul_eq_mul] at h
  have h2 := congrArg (b * ·) h
  rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hb] at h2
  rw [eq_div_iff (pow_ne_zero 2 hb)]; linear_combination h2

omit [FiniteDimensional K5 L] in
private lemma D_ofNat_div (D : Derivation ℤ L L) (a b : ℕ) [a.AtLeastTwo] [b.AtLeastTwo] :
    D ((no_index (OfNat.ofNat a) : L) / (no_index (OfNat.ofNat b) : L)) = 0 := by
  rw [D_div D _ _ (ofNat_ne_zero_L b), D_ofNat, D_ofNat]; ring

omit [FiniteDimensional K5 L] in
private lemma D_one_div (D : Derivation ℤ L L) (b : ℕ) [b.AtLeastTwo] :
    D ((1 : L) / (no_index (OfNat.ofNat b) : L)) = 0 := by
  rw [D_div D _ _ (ofNat_ne_zero_L b), D.map_one_eq_zero, D_ofNat]; ring

-- Convenience abbreviations for K5 coordinates lifted to L
abbrev SL : L := ιL S_K
abbrev QL : L := ιL Q_K
abbrev TL : L := ιL T_K
abbrev xL : L := ιL x_K
abbrev yL : L := ιL y_K

omit [FiniteDimensional K5 L] in
lemma SL_ne : (SL (L := L)) ≠ 0 := (map_ne_zero_iff ιL ιL.injective).mpr S_K_ne_zero
omit [FiniteDimensional K5 L] in
lemma TL_ne : (TL (L := L)) ≠ 0 := (map_ne_zero_iff ιL ιL.injective).mpr T_K_ne_zero
omit [FiniteDimensional K5 L] in
lemma xL_ne : (xL (L := L)) ≠ 0 := (map_ne_zero_iff ιL ιL.injective).mpr x_K_ne_zero
omit [FiniteDimensional K5 L] in
lemma FxL_ne : ιL (L := L) Fx_K ≠ 0 := (map_ne_zero_iff ιL ιL.injective).mpr Fx_K_ne_zero
omit [FiniteDimensional K5 L] in
lemma H0L_ne : ιL (L := L) H0_K ≠ 0 := (map_ne_zero_iff ιL ιL.injective).mpr H0_K_ne_zero
omit [FiniteDimensional K5 L] in
lemma W2L_ne : ιL (L := L) W2_K ≠ 0 := (map_ne_zero_iff ιL ιL.injective).mpr W2_K_ne_zero

-- Match polymorphic *_of functions with ιL of K5 objects
omit [FiniteDimensional K5 L] in
lemma H0_of_L : H0_of (SL (L := L)) QL TL = ιL H0_K := by
  have h1 : H0_K = -2 * S_K ^ 3 + 6 * S_K ^ 2 * Q_K - 3 * S_K * Q_K ^ 2 - 2 * Q_K ^ 3 -
      2 * T_K ^ 3 + 6 * T_K ^ 2 - 3 * T_K - 2 + poly4ToK5 (C (5 / 7 : ℂ)) * Q_K ^ 2 +
      poly4ToK5 (C (10 / 7 : ℂ)) * Q_K := by
    simp only [H0_K, H0_4, H0_3, poly3ToPoly4, map_add, map_sub, map_mul, map_pow, map_neg,
      map_ofNat, eval₂Hom_X', eval₂Hom_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rfl
  have h57 : ιL (L := L) (poly4ToK5 (C (5 / 7 : ℂ))) = (5 / 7 : L) := by
    have hmul : poly4ToK5 (C (5 / 7 : ℂ)) * 7 = 5 := by
      have hC : C (σ := Fin 4) (5 / 7 : ℂ) * 7 = 5 := by
        rw [← map_ofNat C 7, ← map_mul]; norm_num; exact map_ofNat C 5
      have := congrArg poly4ToK5 hC
      simpa only [map_mul, map_ofNat] using this
    have := congrArg (ιL (L := L)) hmul
    simp only [map_mul, map_ofNat] at this
    exact (eq_div_iff (by norm_num : (7 : L) ≠ 0)).mpr this
  have h107 : ιL (L := L) (poly4ToK5 (C (10 / 7 : ℂ))) = (10 / 7 : L) := by
    have hmul : poly4ToK5 (C (10 / 7 : ℂ)) * 7 = 10 := by
      have hC : C (σ := Fin 4) (10 / 7 : ℂ) * 7 = 10 := by
        rw [← map_ofNat C 7, ← map_mul]; norm_num; exact map_ofNat C 10
      have := congrArg poly4ToK5 hC
      simpa only [map_mul, map_ofNat] using this
    have := congrArg (ιL (L := L)) hmul
    simp only [map_mul, map_ofNat] at this
    exact (eq_div_iff (by norm_num : (7 : L) ≠ 0)).mpr this
  rw [h1]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, h57, h107, H0_of, SL, QL, TL]

omit [FiniteDimensional K5 L] in
lemma F5_of_L : F5_of (SL (L := L)) QL TL xL yL = 0 := by
  have h : 3 * SL (L := L) * xL ^ 2 + 3 * TL * yL ^ 2 + ιL H0_K = 0 := by
    have := congrArg (ιL (L := L)) x_K_sq_relation
    simpa only [map_add, map_mul, map_pow, map_ofNat, map_zero, H0_K, SL, TL, xL, yL] using this
  rw [F5_of, H0_of_L]; exact h

omit [FiniteDimensional K5 L] in
lemma DX2_of_L : DX2_of (SL (L := L)) QL xL = ιL DX2_K := by
  simp only [DX2_K, DX2_5, u3_5, toK5, map_add, map_sub, map_mul, map_pow, map_ofNat,
    eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    DX2_of, u3_of, SL, QL, xL]

omit [FiniteDimensional K5 L] in
lemma DY2_of_L : DY2_of (TL (L := L)) yL = ιL DY2_K := by
  simp only [DY2_K, DY2_5, v3_5, toK5, map_add, map_sub, map_mul, map_pow, map_ofNat,
    eval₂Hom_X', Matrix.cons_val,
    DY2_of, v3_of, TL, yL]

omit [FiniteDimensional K5 L] in
lemma W2_of_L : W2_of (SL (L := L)) QL TL xL yL = ιL W2_K := by
  rw [W2_of, DX2_of_L, DY2_of_L]
  simp only [W2_K, W2_5, DX2_K, DY2_K, toK5, map_mul, eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val, SL, TL]

omit [FiniteDimensional K5 L] in
lemma dF5_fn_L (k : Fin 5) :
    dF5_fn k (SL (L := L)) QL TL xL yL = ιL (toK5 (pderiv k F5)) := by
  have hp : ∀ k : Fin 5, toK5 (pderiv k F5) =
      match k with
      | 0 => 3 * x_K ^ 2 + (-6 * S_K ^ 2 + 12 * S_K * Q_K - 3 * Q_K ^ 2)
      | 1 => 6 * S_K ^ 2 - 6 * S_K * Q_K - 6 * Q_K ^ 2 +
          poly4ToK5 (C (10 / 7 : ℂ)) * Q_K + poly4ToK5 (C (10 / 7 : ℂ))
      | 2 => 3 * y_K ^ 2 + (-6 * T_K ^ 2 + 12 * T_K - 3)
      | 3 => 6 * S_K * x_K
      | 4 => 6 * T_K * y_K := by
    intro k
    have h107 : (2 : Poly5) * C (5 / 7 : ℂ) = C (10 / 7 : ℂ) := by
      rw [← map_ofNat C 2, ← map_mul]; norm_num
    match k with
    | 0 =>
      have : pderiv (0 : Fin 5) F5 = 3 * X 3 ^ 2 + (-6 * X 0 ^ 2 + 12 * X 0 * X 1 - 3 * X 1 ^ 2) := by
        simp only [F5, H0_5, H0_4, H0_3, poly4ToPoly5, poly3ToPoly4, tanIdx,
          map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, eval₂Hom_X', eval₂Hom_C,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Derivation.leibniz, Derivation.leibniz_pow, pderiv_ofNat, pderiv_C, pderiv_X,
          smul_eq_mul, nsmul_eq_mul]
        simp; ring
      rw [this]; simp [toK5]
    | 1 =>
      have : pderiv (1 : Fin 5) F5 = 6 * X 0 ^ 2 - 6 * X 0 * X 1 - 6 * X 1 ^ 2 +
          C (10 / 7 : ℂ) * X 1 + C (10 / 7 : ℂ) := by
        simp only [F5, H0_5, H0_4, H0_3, poly4ToPoly5, poly3ToPoly4, tanIdx,
          map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, eval₂Hom_X', eval₂Hom_C,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Derivation.leibniz, Derivation.leibniz_pow, pderiv_ofNat, pderiv_C, pderiv_X,
          smul_eq_mul, nsmul_eq_mul]
        simp only [Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) (by decide : (0 : Fin 5) ≠ 1) 1,
          Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) (by decide : (2 : Fin 5) ≠ 1) 1,
          Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) (by decide : (3 : Fin 5) ≠ 1) 1,
          Pi.single_eq_of_ne (M := fun _ : Fin 5 => Poly5) (by decide : (4 : Fin 5) ≠ 1) 1]
        linear_combination X 1 * h107
      rw [this]
      simp only [toK5, poly4ToK5, map_add, map_sub, map_mul, map_pow, map_ofNat, eval₂Hom_X',
        eval₂Hom_C, Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
    | 2 =>
      have : pderiv (2 : Fin 5) F5 = 3 * X 4 ^ 2 + (-6 * X 2 ^ 2 + 12 * X 2 - 3) := by
        simp only [F5, H0_5, H0_4, H0_3, poly4ToPoly5, poly3ToPoly4, tanIdx,
          map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, eval₂Hom_X', eval₂Hom_C,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Derivation.leibniz, Derivation.leibniz_pow, pderiv_ofNat, pderiv_C, pderiv_X,
          smul_eq_mul, nsmul_eq_mul]
        simp; ring
      rw [this]; simp [toK5]
    | 3 => exact Fx_K_eq
    | 4 => exact pderiv_4_F5
  have h107 : ιL (L := L) (poly4ToK5 (C (10 / 7 : ℂ))) = (10 / 7 : L) := by
    have hmul : poly4ToK5 (C (10 / 7 : ℂ)) * 7 = 10 := by
      have hC : C (σ := Fin 4) (10 / 7 : ℂ) * 7 = 10 := by
        rw [← map_ofNat C 7, ← map_mul]; norm_num; exact map_ofNat C 10
      have := congrArg poly4ToK5 hC
      simpa only [map_mul, map_ofNat] using this
    have := congrArg (ιL (L := L)) hmul
    simp only [map_mul, map_ofNat] at this
    exact (eq_div_iff (by norm_num : (7 : L) ≠ 0)).mpr this
  rw [hp k]
  fin_cases k <;> simp only [
    dF5_fn, dH0_fn, SL, QL, TL, xL, yL, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, h107]

lemma δL_S (i : Fin 4) : δL (L := L) i SL = if i = 0 then 1 else 0 := by
  rw [SL, δL_apply, δ_S]; split_ifs <;> simp

lemma δL_Q (i : Fin 4) : δL (L := L) i QL = if i = 1 then 1 else 0 := by
  rw [QL, δL_apply, δ_Q]; split_ifs <;> simp

lemma δL_T (i : Fin 4) : δL (L := L) i TL = if i = 2 then 1 else 0 := by
  rw [TL, δL_apply, δ_T]; split_ifs <;> simp

lemma δL_y (i : Fin 4) : δL (L := L) i yL = if i = 3 then 1 else 0 := by
  rw [yL, δL_apply, δ_y]; split_ifs <;> simp

lemma δL_x (i : Fin 4) : δL (L := L) i xL = -dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL := by
  rw [xL, δL_apply, δ_x, map_div₀, map_neg, ← dF5_fn_L, Fx_K, ← dF5_fn_L]

-- Chain rule for H_cub and E_fn under ANY derivation D on L
omit [FiniteDimensional K5 L] in
private lemma deriv_H_cub (D : Derivation ℤ L L) (S Q T V0 U V : L) (hV0 : D V0 = 0) :
    D (H_cub S Q T V0 U V) =
      dH_dS S Q U V * D S + dH_dQ S Q V0 U V * D Q + dH_dT T V0 U V * D T +
      dH_dU S Q T V0 U V * D U + dH_dV S Q T V0 U V * D V := by
  simp only [H_cub, dH_dS, dH_dQ, dH_dT, dH_dU, dH_dV,
    map_add, map_sub, map_neg, D.leibniz, D.leibniz_pow, hV0,
    D_ofNat, D_ofNat_div, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  norm_num only
  ring

omit [FiniteDimensional K5 L] in
lemma deriv_E_fn (D : Derivation ℤ L L) (k : Fin 4) (S Q T a b U V : L) :
    D (E_fn k S Q T a b U V) =
      dE_dS k S Q T a b U V * D S + dE_dQ k S Q T a b U V * D Q + dE_dT k S Q T a b U V * D T +
      dE_da k S Q T a b U V * D a + dE_db k S Q T a b U V * D b +
      dE_dU k S Q T a b U V * D U + dE_dV k S Q T a b U V * D V := by
  have h1 : D (1 : L) = 0 := D.map_one_eq_zero
  have h0 : D (0 : L) = 0 := map_zero D
  have h2 : (2 : L) ≠ 0 := by norm_num
  have hdiv2 (z : L) : D (z / 2) = D z / 2 := by
    rw [D_div D z 2 h2, D_ofNat D 2]; field
  fin_cases k
  · simp only [E_fn, dE_dS, dE_dQ, dE_dT, dE_da, dE_db, dE_dU, dE_dV]
    rw [deriv_H_cub D S Q T 1 U V h1]; ring
  · simp only [E_fn, dE_dS, dE_dQ, dE_dT, dE_da, dE_db, dE_dU, dE_dV, map_sub, hdiv2]
    rw [deriv_H_cub D (S + a) (Q + b) (T + 1) 1 U V h1,
        deriv_H_cub D (S - a) (Q - b) (T - 1) 1 U V h1,
        deriv_H_cub D a b 1 0 U V h0]
    simp only [map_add, map_sub, h1]; ring
  · simp only [E_fn, dE_dS, dE_dQ, dE_dT, dE_da, dE_db, dE_dU, dE_dV, map_sub, map_add, hdiv2]
    rw [deriv_H_cub D (S + a) (Q + b) (T + 1) 1 U V h1,
        deriv_H_cub D (S - a) (Q - b) (T - 1) 1 U V h1,
        deriv_H_cub D S Q T 1 U V h1]
    simp only [map_add, map_sub, h1]; ring
  · simp only [E_fn, dE_dS, dE_dQ, dE_dT, dE_da, dE_db, dE_dU, dE_dV]
    rw [deriv_H_cub D a b 1 0 U V h0]; simp only [h1]; ring

-- Weighted residue divergence on L
def resDivW_L (w : Fin 4 → L) : L :=
  ∑ i : Fin 4, (δL i (w i) - w i * δL i (ιL Fx_K) / ιL Fx_K - w i * δL i (ιL W2_K) / (2 * ιL W2_K))

lemma resDivW_L_add (u v : Fin 4 → L) :
    resDivW_L (fun i => u i + v i) = resDivW_L u + resDivW_L v := by
  simp only [resDivW_L, map_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

lemma resDivW_L_smul (g : L) (w : Fin 4 → L) :
    resDivW_L (fun i => g * w i) = g * resDivW_L w + ∑ i : Fin 4, δL i g * w i := by
  simp only [resDivW_L, (δL _).leibniz, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

-- 3-form contraction vector w(α) = iota^{-1}(α ∧ dU ∧ dV)
def w_of_1form (α : Fin 5 → L) (JS JQ JT : L) : Fin 4 → L :=
  let Fx := dF5_fn 3 SL QL TL xL yL
  let Fy := dF5_fn 4 SL QL TL xL yL
  let FS := dF5_fn 0 SL QL TL xL yL
  let FQ := dF5_fn 1 SL QL TL xL yL
  let FT := dF5_fn 2 SL QL TL xL yL
  let cy := Fx * α 4 - Fy * α 3
  ![cy * JS, cy * JQ, cy * JT,
    -((Fx * α 0 - FS * α 3) * JS + (Fx * α 1 - FQ * α 3) * JQ + (Fx * α 2 - FT * α 3) * JT)]

omit [FiniteDimensional K5 L] in
lemma w_of_1form_add (α β : Fin 5 → L) (JS JQ JT : L) :
    w_of_1form (fun k => α k + β k) JS JQ JT =
      fun i => w_of_1form α JS JQ JT i + w_of_1form β JS JQ JT i := by
  funext i; fin_cases i <;> simp [w_of_1form] <;> ring

omit [FiniteDimensional K5 L] in
lemma w_of_1form_smul (g : L) (α : Fin 5 → L) (JS JQ JT : L) :
    w_of_1form (fun k => g * α k) JS JQ JT = fun i => g * w_of_1form α JS JQ JT i := by
  funext i; fin_cases i <;> simp [w_of_1form] <;> ring

-- Universal 3-form divergence formula for any 1-form α whose δL derivatives split into (S,Q,T,x,y) + (U,V) parts!
lemma resDivW_L_w_of_1form (α : Fin 5 → L) (dα : Fin 5 → Fin 5 → L) (dαU dαV : Fin 5 → L)
    (U V JS JQ JT : L)
    (hJ_div : δL 0 JS + δL 1 JQ + δL 2 JT = 0)
    (hJ_y : δL 3 JS = 0 ∧ δL 3 JQ = 0 ∧ δL 3 JT = 0)
    (hU_J : JS * δL 0 U + JQ * δL 1 U + JT * δL 2 U = 0)
    (hV_J : JS * δL 0 V + JQ * δL 1 V + JT * δL 2 V = 0)
    (hU_y : δL 3 U = 0) (hV_y : δL 3 V = 0)
    (hδ_α : ∀ (i : Fin 4) (k : Fin 5),
      δL i (α k) = dα k (tanIdx i) - (dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dα k 3 +
        dαU k * δL i U + dαV k * δL i V) :
    resDivW_L (w_of_1form α JS JQ JT) =
      -(F_contract SL QL TL xL yL
          (fun p q => 2 * ιL W2_K * (dα q p - dα p q) -
            (α q * dW2_fn p SL QL TL xL yL - α p * dW2_fn q SL QL TL xL yL)) 0 * JS +
        F_contract SL QL TL xL yL
          (fun p q => 2 * ιL W2_K * (dα q p - dα p q) -
            (α q * dW2_fn p SL QL TL xL yL - α p * dW2_fn q SL QL TL xL yL)) 1 * JQ +
        F_contract SL QL TL xL yL
          (fun p q => 2 * ιL W2_K * (dα q p - dα p q) -
            (α q * dW2_fn p SL QL TL xL yL - α p * dW2_fn q SL QL TL xL yL)) 2 * JT) /
        (2 * ιL W2_K) := by
  have hFx_eq : ιL (L := L) Fx_K = dF5_fn 3 SL QL TL xL yL := by rw [Fx_K, ← dF5_fn_L]
  have hFx_ne : dF5_fn 3 (SL (L := L)) QL TL xL yL ≠ 0 := by rw [← hFx_eq]; exact FxL_ne
  have hW2_ne : ιL (L := L) W2_K ≠ 0 := W2L_ne
  -- Compute δL i of dF5_fn k and W2_K!
  have hδF (i : Fin 4) (k : Fin 5) :
      δL (L := L) i (dF5_fn k SL QL TL xL yL) =
        (match k, tanIdx i with
         | 0, 0 => -12 * SL + 12 * QL | 0, 1 => 12 * SL - 6 * QL | 0, 2 => 0 | 0, 4 => 0
         | 1, 0 => 12 * SL - 6 * QL | 1, 1 => -6 * SL - 12 * QL + 10 / 7 | 1, 2 => 0 | 1, 4 => 0
         | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => -12 * TL + 12 | 2, 4 => 6 * yL
         | 3, 0 => 6 * xL | 3, 1 => 0 | 3, 2 => 0 | 3, 4 => 0
         | 4, 0 => 0 | 4, 1 => 0 | 4, 2 => 6 * yL | 4, 4 => 6 * TL
         | _, _ => 0) -
        (dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) *
        (match k with | 0 => 6 * xL | 3 => 6 * SL | _ => 0) := by
    fin_cases i <;> fin_cases k <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
         dF5_fn, dH0_fn, tanIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
         map_add, map_sub, map_neg, (δL _).leibniz, (δL _).leibniz_pow,
         D_ofNat, D_ofNat_div, δL_S, δL_Q, δL_T, δL_y, δL_x,
         Fin.reduceEq, ↓reduceIte,
         smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat];
       norm_num only; ring)
  have hδW2 (i : Fin 4) :
      δL (L := L) i (ιL W2_K) = dW2_fn (tanIdx i) SL QL TL xL yL -
        (dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dW2_fn 3 SL QL TL xL yL := by
    rw [← W2_of_L]
    fin_cases i <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
         W2_of, DX2_of, DY2_of, u3_of, v3_of, dW2_fn, dDX2_fn, dDY2_fn, tanIdx,
         Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
         map_add, map_sub, (δL _).leibniz, (δL _).leibniz_pow,
         D_ofNat, δL_S, δL_Q, δL_T, δL_y, δL_x, Fin.reduceEq, ↓reduceIte,
         smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat];
       norm_num only; ring)
  -- Expand resDivW_L over Fin 4!
  rw [resDivW_L, Fin.sum_univ_four]
  simp only [w_of_1form, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    hFx_eq, hδW2, map_neg, map_add, map_sub, (δL _).leibniz, smul_eq_mul,
    hδF, hδ_α, hJ_y.1, hJ_y.2.1, hJ_y.2.2, hU_y, hV_y, tanIdx, F_contract]
  -- Abstract out all atomic variables so `field` + `linear_combination` finishes in 0.1s!
  have h2W2 : (2 * ιL (L := L) W2_K) ≠ 0 := mul_ne_zero (by norm_num) hW2_ne
  rw [eq_div_iff h2W2]
  field_simp [hFx_ne, hW2_ne]
  have hS0 := hJ_div; have hU0 := hU_J; have hV0 := hV_J
  -- Wait: every single mixed 2nd derivative of F5 cancels identically, plus hJ_div, hU_J, hV_J!
  -- Generalize every non-structural expression to keep the polynomial small:
  generalize δL 0 JS = jS0 at hS0 ⊢; generalize δL 1 JQ = jQ1 at hS0 ⊢; generalize δL 2 JT = jT2 at hS0 ⊢
  generalize δL 0 U = u0 at hU0 ⊢; generalize δL 1 U = u1 at hU0 ⊢; generalize δL 2 U = u2 at hU0 ⊢
  generalize δL 0 V = v0 at hV0 ⊢; generalize δL 1 V = v1 at hV0 ⊢; generalize δL 2 V = v2 at hV0 ⊢
  generalize dF5_fn 0 (SL (L := L)) QL TL xL yL = F0; generalize dF5_fn 1 (SL (L := L)) QL TL xL yL = F1
  generalize dF5_fn 2 (SL (L := L)) QL TL xL yL = F2; generalize dF5_fn 3 (SL (L := L)) QL TL xL yL = F3
  generalize dF5_fn 4 (SL (L := L)) QL TL xL yL = F4
  generalize dW2_fn 0 (SL (L := L)) QL TL xL yL = W0; generalize dW2_fn 1 (SL (L := L)) QL TL xL yL = W1
  generalize dW2_fn 2 (SL (L := L)) QL TL xL yL = W2_; generalize dW2_fn 3 (SL (L := L)) QL TL xL yL = W3
  generalize dW2_fn 4 (SL (L := L)) QL TL xL yL = W4
  generalize ιL (L := L) W2_K = W2
  linear_combination
    2 * W2 * F3 ^ 2 * (F3 * α 4 - F4 * α 3) * hS0 +
    2 * W2 * F3 ^ 2 * (F3 * dαU 4 - F4 * dαU 3) * hU0 +
    2 * W2 * F3 ^ 2 * (F3 * dαV 4 - F4 * dαV 3) * hV0

private lemma deriv_DX2_L (i : Fin 4) :
    δL (L := L) i (DX2_of SL QL xL) = dDX2_fn (tanIdx i) SL QL xL -
      (dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dDX2_fn 3 SL QL xL := by
  fin_cases i <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
       DX2_of, dDX2_fn, u3_of, tanIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
       map_add, map_sub, (δL _).leibniz, (δL _).leibniz_pow, D_ofNat,
       δL_S, δL_Q, δL_x, Fin.reduceEq, ↓reduceIte,
       smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat];
     norm_num only; ring)

private lemma deriv_DY2_L (i : Fin 4) :
    δL (L := L) i (DY2_of TL yL) = dDY2_fn (tanIdx i) TL yL -
      (dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dDY2_fn 3 TL yL := by
  fin_cases i <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
       DY2_of, dDY2_fn, v3_of, tanIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
       map_add, map_sub, (δL _).leibniz, (δL _).leibniz_pow, D_ofNat,
       δL_T, δL_y, Fin.reduceEq, ↓reduceIte,
       smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat];
     norm_num only; ring)

-- Specialization to α = PhiY / G and α = PhiX / G!
private lemma deriv_G_L (i : Fin 4) (U V : L) :
    δL (L := L) i (G_of SL QL TL xL yL U V) =
      dG_fn (tanIdx i) SL QL TL xL yL U V -
        (dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dG_fn 3 SL QL TL xL yL U V +
      (DX2_of SL QL xL / 9) * δL i U + (DY2_of TL yL / 9) * δL i V := by
  have h9 : (9 : L) ≠ 0 := by norm_num
  have hdu : δL (L := L) i (u_of U) = δL i U / 9 := by
    rw [u_of, D_div _ _ _ h9, map_sub, (δL i).map_one_eq_zero, D_ofNat]; field
  have hdv : δL (L := L) i (v_of V) = δL i V / 9 := by
    rw [v_of, D_div _ _ _ h9, map_sub, (δL i).map_one_eq_zero, D_ofNat]; field
  rw [G_of, map_add, (δL i).leibniz, (δL i).leibniz, hdu, hdv]
  simp only [smul_eq_mul, deriv_DX2_L, deriv_DY2_L, dG_fn]; ring

-- Explicit U- and V-partial derivatives of br_fn (independent of i : Fin 4!)
private def dLX_dU (S Q x : L) : L := u3_of S Q x + (2 / 27) * S - (1 / 3) * Q
private def dLY_dV (T y : L) : L := v3_of T y + (2 / 27) * T - 1 / 3

private def ddLX_dU (k : Fin 5) : L :=
  match k with | 0 => -(25 / 27) | 1 => 5 / 3 | 3 => 1 | _ => 0

private def ddLY_dV (k : Fin 5) : L :=
  match k with | 2 => -(25 / 27) | 4 => 1 | _ => 0

private def dbr_dU (k : Fin 5) (S Q T x y _U V : L) : L :=
  let dlx := dLX_dU S Q x; let ly := LY_of T y V
  let base : L := match k with | 0 => -T * dlx * ly | 2 => S * dlx * ly | _ => 0
  base + 2 * S * T * (dlx * dLY_fn k V - ly * ddLX_dU k)

private def dbr_dV (k : Fin 5) (S Q T x y U _V : L) : L :=
  let lx := LX_of S Q x U; let dly := dLY_dV T y
  let base : L := match k with | 0 => -T * lx * dly | 2 => S * lx * dly | _ => 0
  base + 2 * S * T * (lx * ddLY_dV k - dly * dLX_fn k U)

private lemma deriv_br_L (i : Fin 4) (k : Fin 5) (U V : L) :
    δL (L := L) i (br_fn k SL QL TL xL yL U V) =
      dbr_fn k (tanIdx i) SL QL TL xL yL U V -
        (dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dbr_fn k 3 SL QL TL xL yL U V +
      dbr_dU k SL QL TL xL yL U V * δL i U + dbr_dV k SL QL TL xL yL U V * δL i V := by
  have h9 : (9 : L) ≠ 0 := by norm_num
  have h3 : (3 : L) ≠ 0 := by norm_num
  have hdiv3 (j : Fin 4) (z : L) : δL (L := L) j (z / 3) = δL j z / 3 := by
    rw [D_div _ _ _ h3, D_ofNat]; field
  have hdu (j : Fin 4) : δL (L := L) j (u_of U) = δL j U / 9 := by
    rw [u_of, D_div _ _ _ h9, map_sub, (δL j).map_one_eq_zero, D_ofNat]; field
  have hdv (j : Fin 4) : δL (L := L) j (v_of V) = δL j V / 9 := by
    rw [v_of, D_div _ _ _ h9, map_sub, (δL j).map_one_eq_zero, D_ofNat]; field
  have hLX (j : Fin 4) : δL (L := L) j (LX_of SL QL xL U) =
      dLX_fn (tanIdx j) U - (dF5_fn (tanIdx j) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dLX_fn 3 U +
        dLX_dU SL QL xL * δL j U := by
    fin_cases j <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
         LX_of, u3_of, dLX_fn, dLX_dU, tanIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
         map_add, map_sub, hdiv3, (δL _).leibniz, hdu, D_ofNat, δL_S, δL_Q, δL_x,
         Fin.reduceEq, ↓reduceIte, smul_eq_mul];
       ring)
  have hLY (j : Fin 4) : δL (L := L) j (LY_of TL yL V) =
      dLY_fn (tanIdx j) V - (dF5_fn (tanIdx j) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dLY_fn 3 V +
        dLY_dV TL yL * δL j V := by
    fin_cases j <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
         LY_of, v3_of, dLY_fn, dLY_dV, tanIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
         map_add, map_sub, hdiv3, (δL _).leibniz, hdv, D_ofNat, δL_T, δL_y,
         Fin.reduceEq, ↓reduceIte, smul_eq_mul];
       ring)
  have hdLX (j : Fin 4) (k' : Fin 5) : δL (L := L) j (dLX_fn k' U) = ddLX_dU k' * δL j U := by
    fin_cases k' <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
         dLX_fn, ddLX_dU, map_add, map_sub, map_neg, hdiv3, (δL _).leibniz, hdu, D_ofNat, map_zero, smul_eq_mul];
       ring)
  have hdLY (j : Fin 4) (k' : Fin 5) : δL (L := L) j (dLY_fn k' V) = ddLY_dV k' * δL j V := by
    fin_cases k' <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
         dLY_fn, ddLY_dV, map_add, map_neg, hdiv3, (δL _).leibniz, hdv, D_ofNat, map_zero, smul_eq_mul];
       ring)
  fin_cases i <;> fin_cases k <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
       br_fn, dbr_fn, dbr_dU, dbr_dV, tanIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
       map_add, map_sub, map_neg, (δL _).leibniz, hLX, hLY, hdLX, hdLY, D_ofNat, δL_S, δL_T,
       Fin.reduceEq, ↓reduceIte, smul_eq_mul, map_zero];
     ring)

private lemma resDivW_L_Phi_div_G (Phi : Fin 5 → L) (dPhi : Fin 5 → Fin 5 → L)
    (dPhiU dPhiV : Fin 5 → L) (U V JS JQ JT : L)
    (hG : G_of SL QL TL xL yL U V ≠ 0)
    (hJ_div : δL 0 JS + δL 1 JQ + δL 2 JT = 0)
    (hJ_y : δL 3 JS = 0 ∧ δL 3 JQ = 0 ∧ δL 3 JT = 0)
    (hU_J : JS * δL 0 U + JQ * δL 1 U + JT * δL 2 U = 0)
    (hV_J : JS * δL 0 V + JQ * δL 1 V + JT * δL 2 V = 0)
    (hU_y : δL 3 U = 0) (hV_y : δL 3 V = 0)
    (hδ_Phi : ∀ (i : Fin 4) (k : Fin 5),
      δL i (Phi k) = dPhi k (tanIdx i) - (dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dPhi k 3 +
        dPhiU k * δL i U + dPhiV k * δL i V) :
    resDivW_L (w_of_1form (fun k => Phi k / G_of SL QL TL xL yL U V) JS JQ JT) =
      -(F_contract SL QL TL xL yL (curl_num_fn Phi dPhi SL QL TL xL yL U V) 0 * JS +
        F_contract SL QL TL xL yL (curl_num_fn Phi dPhi SL QL TL xL yL U V) 1 * JQ +
        F_contract SL QL TL xL yL (curl_num_fn Phi dPhi SL QL TL xL yL U V) 2 * JT) /
        (2 * ιL W2_K * G_of SL QL TL xL yL U V ^ 2) := by
  let G := G_of (SL (L := L)) QL TL xL yL U V
  let dα : Fin 5 → Fin 5 → L := fun k j => (G * dPhi k j - Phi k * dG_fn j SL QL TL xL yL U V) / G ^ 2
  let dαU : Fin 5 → L := fun k => (G * dPhiU k - Phi k * (DX2_of SL QL xL / 9)) / G ^ 2
  let dαV : Fin 5 → L := fun k => (G * dPhiV k - Phi k * (DY2_of TL yL / 9)) / G ^ 2
  have hδ_α (i : Fin 4) (k : Fin 5) :
      δL i (Phi k / G) = dα k (tanIdx i) - (dF5_fn (tanIdx i) SL QL TL xL yL / dF5_fn 3 SL QL TL xL yL) * dα k 3 +
        dαU k * δL i U + dαV k * δL i V := by
    rw [D_div (δL i) (Phi k) G hG, hδ_Phi i k, deriv_G_L i U V]
    dsimp only [dα, dαU, dαV, G]; ring
  rw [resDivW_L_w_of_1form (fun k => Phi k / G) dα dαU dαV U V JS JQ JT hJ_div hJ_y hU_J hV_J hU_y hV_y hδ_α]
  have h2W2 : (2 * ιL (L := L) W2_K) ≠ 0 := mul_ne_zero (by norm_num) W2L_ne
  have hG2 : G ^ 2 ≠ 0 := pow_ne_zero 2 hG
  have hpair (p q : Fin 5) :
      2 * ιL W2_K * (dα q p - dα p q) -
        (Phi q / G * dW2_fn p SL QL TL xL yL - Phi p / G * dW2_fn q SL QL TL xL yL) =
      curl_num_fn Phi dPhi SL QL TL xL yL U V p q / G ^ 2 := by
    rw [curl_num_fn, W2_of_L]
    dsimp only [dα, G]
    field_simp [hG]; ring
  simp_rw [F_contract, hpair]
  have hG' : G ≠ 0 := hG
  have hW2' : ιL (L := L) W2_K ≠ 0 := W2L_ne
  change _ = _ / (2 * ιL W2_K * G ^ 2)
  field_simp [h2W2, hW2', hG2, hG']

lemma resDivW_L_PhiY_div_G (U V JS JQ JT : L)
    (hG : G_of SL QL TL xL yL U V ≠ 0)
    (hJ_div : δL 0 JS + δL 1 JQ + δL 2 JT = 0)
    (hJ_y : δL 3 JS = 0 ∧ δL 3 JQ = 0 ∧ δL 3 JT = 0)
    (hU_J : JS * δL 0 U + JQ * δL 1 U + JT * δL 2 U = 0)
    (hV_J : JS * δL 0 V + JQ * δL 1 V + JT * δL 2 V = 0)
    (hU_y : δL 3 U = 0) (hV_y : δL 3 V = 0) :
    resDivW_L (w_of_1form (fun k => PhiY_fn k SL QL TL xL yL U V / G_of SL QL TL xL yL U V) JS JQ JT) =
      -(CY_of SL QL TL xL yL U V 0 * JS + CY_of SL QL TL xL yL U V 1 * JQ + CY_of SL QL TL xL yL U V 2 * JT) /
        (2 * ιL W2_K * G_of SL QL TL xL yL U V ^ 2) := by
  apply resDivW_L_Phi_div_G (fun k => PhiY_fn k SL QL TL xL yL U V)
    (fun k j => dPhiY_fn k j SL QL TL xL yL U V)
    (fun k => DY2_of TL yL * dbr_dU k SL QL TL xL yL U V)
    (fun k => DY2_of TL yL * dbr_dV k SL QL TL xL yL U V)
    U V JS JQ JT hG hJ_div hJ_y hU_J hV_J hU_y hV_y
  intro i k
  rw [PhiY_fn, (δL i).leibniz, deriv_br_L i k U V, deriv_DY2_L i, dPhiY_fn, dPhiY_fn]
  simp only [smul_eq_mul]; ring

lemma resDivW_L_PhiX_div_G (U V JS JQ JT : L)
    (hG : G_of SL QL TL xL yL U V ≠ 0)
    (hJ_div : δL 0 JS + δL 1 JQ + δL 2 JT = 0)
    (hJ_y : δL 3 JS = 0 ∧ δL 3 JQ = 0 ∧ δL 3 JT = 0)
    (hU_J : JS * δL 0 U + JQ * δL 1 U + JT * δL 2 U = 0)
    (hV_J : JS * δL 0 V + JQ * δL 1 V + JT * δL 2 V = 0)
    (hU_y : δL 3 U = 0) (hV_y : δL 3 V = 0) :
    resDivW_L (w_of_1form (fun k => PhiX_fn k SL QL TL xL yL U V / G_of SL QL TL xL yL U V) JS JQ JT) =
      -(CX_of SL QL TL xL yL U V 0 * JS + CX_of SL QL TL xL yL U V 1 * JQ + CX_of SL QL TL xL yL U V 2 * JT) /
        (2 * ιL W2_K * G_of SL QL TL xL yL U V ^ 2) := by
  apply resDivW_L_Phi_div_G (fun k => PhiX_fn k SL QL TL xL yL U V)
    (fun k j => dPhiX_fn k j SL QL TL xL yL U V)
    (fun k => -DX2_of SL QL xL * dbr_dU k SL QL TL xL yL U V)
    (fun k => -DX2_of SL QL xL * dbr_dV k SL QL TL xL yL U V)
    U V JS JQ JT hG hJ_div hJ_y hU_J hV_J hU_y hV_y
  intro i k
  rw [PhiX_fn, (δL i).leibniz, map_neg, deriv_br_L i k U V, deriv_DX2_L i, dPhiX_fn, dPhiX_fn]
  simp only [smul_eq_mul]; ring

-- Helper: any derivation D on L killing (a, b, ξS, ξQ, U, V) kills A_0U, A_0V, A_Y, A_X, det(S_ab_mat)!
omit [FiniteDimensional K5 L] in
private lemma D_kills_dH_dS (D : Derivation ℤ L L) (s q U V : L)
    (hs : D s = 0) (hq : D q = 0) (hU : D U = 0) (hV : D V = 0) :
    D (dH_dS s q U V) = 0 := by
  simp only [dH_dS, map_add, map_sub, map_neg, D.leibniz, D.leibniz_pow, hs, hq, hU, hV,
    D_ofNat, D_ofNat_div, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]

omit [FiniteDimensional K5 L] in
private lemma D_kills_dH_dQ (D : Derivation ℤ L L) (s q v0 U V : L)
    (hs : D s = 0) (hq : D q = 0) (hv0 : D v0 = 0) (hU : D U = 0) (hV : D V = 0) :
    D (dH_dQ s q v0 U V) = 0 := by
  simp only [dH_dQ, map_add, map_sub, map_neg, D.leibniz, D.leibniz_pow, hs, hq, hv0, hU, hV,
    D_ofNat, D_ofNat_div, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]

omit [FiniteDimensional K5 L] in
private lemma D_kills_q_coeffs (D : Derivation ℤ L L) (a b ξS ξQ U V : L)
    (ha : D a = 0) (hb : D b = 0) (hξS : D ξS = 0) (hξQ : D ξQ = 0) (hU : D U = 0) (hV : D V = 0) :
    D (q1_a2 a b U V) = 0 ∧ D (q1_a1 a b ξS ξQ U V) = 0 ∧ D (q1_a0 ξS ξQ U V) = 0 ∧
    D (q2_b2 a b U V) = 0 ∧ D (q2_b1 a b ξS ξQ U V) = 0 ∧ D (q2_b0 ξS ξQ U V) = 0 := by
  have h0 : D (0 : L) = 0 := map_zero D
  have h1 : D (1 : L) = 0 := D.map_one_eq_zero
  have haS : D (a + ξS) = 0 := by rw [map_add, ha, hξS, add_zero]
  have hbQ : D (b + ξQ) = 0 := by rw [map_add, hb, hξQ, add_zero]
  refine ⟨D_kills_dH_dS D a b U V ha hb hU hV, ?_, D_kills_dH_dS D ξS ξQ U V hξS hξQ hU hV,
    D_kills_dH_dQ D a b 0 U V ha hb h0 hU hV, ?_, D_kills_dH_dQ D ξS ξQ 1 U V hξS hξQ h1 hU hV⟩
  · simp only [q1_a1, map_sub, D_kills_dH_dS D (a + ξS) (b + ξQ) U V haS hbQ hU hV,
      D_kills_dH_dS D a b U V ha hb hU hV, D_kills_dH_dS D ξS ξQ U V hξS hξQ hU hV, sub_zero]
  · simp only [q2_b1, map_add, map_sub, D.leibniz,
      D_kills_dH_dQ D (a + ξS) (b + ξQ) 0 U V haS hbQ h0 hU hV,
      D_kills_dH_dQ D a b 0 U V ha hb h0 hU hV,
      D_kills_dH_dQ D ξS ξQ 0 U V hξS hξQ h0 hU hV,
      D_ofNat_div, hb, hU, hV, smul_eq_mul, mul_zero, add_zero, sub_zero]

omit [FiniteDimensional K5 L] in
private lemma D_kills_numM (D : Derivation ℤ L L) (mi : Fin 10) (a b ξS ξQ U V : L)
    (ha : D a = 0) (hb : D b = 0) (hξS : D ξS = 0) (hξQ : D ξQ = 0) (hU : D U = 0) (hV : D V = 0) :
    D (numM mi a b ξS ξQ U V) = 0 := by
  obtain ⟨ha2, ha1, ha0, hb2, hb1, hb0⟩ := D_kills_q_coeffs D a b ξS ξQ U V ha hb hξS hξQ hU hV
  fin_cases mi <;>
    simp only [numM, map_add, map_sub, D.leibniz, D.leibniz_pow, ha, hb, hξS, hξQ,
      ha2, ha1, ha0, hb2, hb1, hb0, D_ofNat, D_one_div,
      D.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, sub_zero]

omit [FiniteDimensional K5 L] in
private lemma D_kills_weights (D : Derivation ℤ L L) (a b ξS ξQ U V : L)
    (ha : D a = 0) (hb : D b = 0) (hξS : D ξS = 0) (hξQ : D ξQ = 0) (hU : D U = 0) (hV : D V = 0) :
    D (A_0U a b ξS ξQ U V) = 0 ∧ D (A_0V a b ξS ξQ U V) = 0 ∧
    D (A_Y a b ξS ξQ U V) = 0 ∧ D (A_X a b ξS ξQ U V) = 0 ∧
    D ((S_ab_mat a b ξS ξQ U V).det) = 0 := by
  have hm (mi : Fin 10) : D (numM mi a b ξS ξQ U V) = 0 :=
    D_kills_numM D mi a b ξS ξQ U V ha hb hξS hξQ hU hV
  obtain ⟨ha2, ha1, ha0, hb2, hb1, hb0⟩ := D_kills_q_coeffs D a b ξS ξQ U V ha hb hξS hξQ hU hV
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [A_0U, map_add, map_sub, map_neg, D.leibniz, hm, D_ofNat, D_ofNat_div,
      smul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]
  · simp only [A_0V, map_add, map_sub, map_neg, D.leibniz, hm, D_ofNat, D_ofNat_div,
      smul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]
  · simp only [A_Y, map_add, map_sub, map_neg, D.leibniz, hm, hU, hV, D_ofNat, D_ofNat_div,
      smul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]
  · simp only [A_X, map_add, map_sub, map_neg, D.leibniz, hm, hU, D_ofNat, D_ofNat_div,
      smul_eq_mul, mul_zero, add_zero, sub_zero, neg_zero]
  · rw [Matrix.det_apply]
    rw [map_sum]
    apply Finset.sum_eq_zero; intro σ _
    rw [Units.smul_def, zsmul_eq_mul, D.leibniz, D.map_intCast, smul_zero, add_zero]
    suffices hprod : D (∏ i : Fin 4, S_ab_mat a b ξS ξQ U V (σ i) i) = 0 by rw [hprod, smul_zero]
    rw [Fin.prod_univ_four]
    have hent (r c : Fin 4) : D (S_ab_mat a b ξS ξQ U V r c) = 0 := by
      fin_cases r <;> fin_cases c <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, S_ab_mat,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          map_zero, ha2, ha1, ha0, hb2, hb1, hb0]
    simp only [D.leibniz, hent, smul_eq_mul, mul_zero, add_zero]

/-! ### Section 5: The Explicit Horizontal Vector `w_horiz` and Main Sheet Theorem -/

def w_horiz (a b U V : L) : Fin 4 → L :=
  let JS := δL 1 U * δL 2 V - δL 2 U * δL 1 V
  let JQ := δL 2 U * δL 0 V - δL 0 U * δL 2 V
  let JT := δL 0 U * δL 1 V - δL 1 U * δL 0 V
  let ξS := SL - a * TL; let ξQ := QL - b * TL
  let dM := (M_abSQ SL QL TL a b U V).det
  let f0 := (A_0U a b ξS ξQ U V / U + A_0V a b ξS ξQ U V / V) / (81 * dM)
  let fY := A_Y a b ξS ξQ U V / (81 * dM)
  let fX := A_X a b ξS ξQ U V / (81 * dM)
  let G := G_of SL QL TL xL yL U V
  let H0 := H0_of SL QL TL
  let alY := fun k => PhiY_fn k SL QL TL xL yL U V / G
  let alX := fun k => PhiX_fn k SL QL TL xL yL U V / G
  let al0 := fun k => (A1_of SL QL U V / H0) * alY k + (B1_of TL U V / H0) * alX k
  fun i => f0 * w_of_1form al0 JS JQ JT i + fY * w_of_1form alY JS JQ JT i + fX * w_of_1form alX JS JQ JT i


end SheetL
end SymmetricSexticResidual.SheetCalculus


