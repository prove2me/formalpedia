-- Prove2me | Definitions.Def_HodgeComputerSSR_BivReduce
-- name    : HodgeComputerSSR_BivReduce
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T10:09:40.54725+00:00
-- url     : https://prove2.me/theorems/490f6762-d304-4052-9271-e9b68cd4b786
-- title:
--   Unconditional mod-$F_5$ bivariate reduction `bivReduceX2`
-- statement:
--   Defines exact sparse bivariate reduction `bivReduceX2` eliminating $x^2$ using $21 S x^2 + 21 T y^2 + 7 H_0 = 0$ in $K_5$ and proves its soundness lemma `evalBivK5_bivReduceX2`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L81-L150

import Definitions.Def_HodgeComputerSSR_VerticalData
import Definitions.Def_HodgeComputerSSR_BivEval

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.VerticalIdentity
  PolynomialEncoding.KroneckerCheck
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

lemma ringEval_vK5_H0_int_e : ringEval vK5 H0_int_e = 7 * H0_K := by
  have hH0 : H0_K =
      -2 * S_K ^ 3 + 6 * S_K ^ 2 * Q_K - 3 * S_K * Q_K ^ 2 - 2 * Q_K ^ 3 -
      2 * T_K ^ 3 + 6 * T_K ^ 2 - 3 * T_K - 2 +
      5 / 7 * Q_K ^ 2 + 10 / 7 * Q_K := by
    rw [H0_K, ← toK5_poly4, H0_4, H0_3, poly3ToPoly4]
    simp only [toK5, poly4ToPoly5, tanIdx, map_add, map_sub, map_mul, map_pow, map_neg,
      map_ofNat, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, poly4ToK5, k4ToK5]
    have h57 : (algebraMap Poly4 K4 (MvPolynomial.C (5 / 7 : ℂ))) = (5 / 7 : K4) := by
      have h7 : (7 : K4) ≠ 0 := by exact_mod_cast (by decide : (7 : ℕ) ≠ 0)
      apply mul_left_cancel₀ h7
      have h1 : (7 : K4) * algebraMap Poly4 K4 (MvPolynomial.C (5 / 7 : ℂ)) =
          algebraMap Poly4 K4 (MvPolynomial.C (7 * (5 / 7 : ℂ))) := by
        rw [← map_ofNat (algebraMap Poly4 K4) 7, ← map_mul, ← map_ofNat MvPolynomial.C 7, ← map_mul]
      rw [h1, show (7 : ℂ) * (5 / 7 : ℂ) = 5 by norm_num, map_ofNat, map_ofNat, mul_div_cancel₀ _ h7]
    have h107 : (algebraMap Poly4 K4 (MvPolynomial.C (10 / 7 : ℂ))) = (10 / 7 : K4) := by
      have h7 : (7 : K4) ≠ 0 := by exact_mod_cast (by decide : (7 : ℕ) ≠ 0)
      apply mul_left_cancel₀ h7
      have h1 : (7 : K4) * algebraMap Poly4 K4 (MvPolynomial.C (10 / 7 : ℂ)) =
          algebraMap Poly4 K4 (MvPolynomial.C (7 * (10 / 7 : ℂ))) := by
        rw [← map_ofNat (algebraMap Poly4 K4) 7, ← map_mul, ← map_ofNat MvPolynomial.C 7, ← map_mul]
      rw [h1, show (7 : ℂ) * (10 / 7 : ℂ) = 10 by norm_num, map_ofNat, map_ofNat, mul_div_cancel₀ _ h7]
    rw [h57, h107]; simp only [map_div₀, map_ofNat]
  rw [hH0, H0_int_e]
  simp only [ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]
  ring

lemma K5_21_S_x_sq : 21 * S_K * x_K ^ 2 = -(21 * T_K * y_K ^ 2 + ringEval vK5 H0_int_e) := by
  rw [ringEval_vK5_H0_int_e]
  have h := x_K_sq_relation
  change 3 * S_K * x_K ^ 2 + 3 * T_K * y_K ^ 2 + H0_K = 0 at h
  linear_combination 7 * h

/-- Single-pass mod-`F5` `x^2`-reduction on `Biv` (multiplies denotation by `21 * S_K`). -/
def bivReduceX2 : Biv → Biv
  | .nil => .nil
  | .cons a i j p =>
    let rest := bivReduceX2 p
    match i with
    | 0 => merge 512 (.cons (.mul (.mul (.num 21) eS) a) 0 j .nil) rest
    | 1 => merge 512 (.cons (.mul (.mul (.num 21) eS) a) 1 j .nil) rest
    | i' + 2 =>
      let t1 := .cons (.mul (.mul (.num (-21)) eT) a) i' (j + 2) .nil
      let t2 := .cons (.mul (.neg H0_int_e) a) i' j .nil
      merge 512 (merge 512 t1 t2) rest

lemma evalBivK5_bivReduceX2 (p : Biv) :
    evalBivK5 (bivReduceX2 p) = 21 * S_K * evalBivK5 p := by
  induction p with
  | nil => simp [bivReduceX2, evalBivK5, denote]
  | cons a i j p ih =>
    rcases i with _ | _ | i'
    · simp only [bivReduceX2, evalBivK5, merge_denote, denote, ringEval, eS, vK5, Int.cast_ofNat,
        add_zero, pow_zero, mul_one] at ih ⊢
      rw [ih]; ring
    · simp only [bivReduceX2, evalBivK5, merge_denote, denote, ringEval, eS, vK5, Int.cast_ofNat,
        add_zero, pow_one] at ih ⊢
      rw [ih]; ring
    · simp only [bivReduceX2, evalBivK5, merge_denote, denote, ringEval, eT, vK5,
        Int.cast_neg, Int.cast_ofNat, add_zero] at ih ⊢
      rw [ih]
      have hsq : x_K ^ (i' + 2) = x_K ^ i' * x_K ^ 2 := by rw [pow_add]
      have hy : y_K ^ (j + 2) = y_K ^ j * y_K ^ 2 := by rw [pow_add]
      rw [hsq, hy]
      linear_combination -(ringEval vK5 a * x_K ^ i' * y_K ^ j) * K5_21_S_x_sq

lemma evalBivK5_bivAdd (p q : Biv) : evalBivK5 (bivAdd p q) = evalBivK5 p + evalBivK5 q :=
  merge_denote vK5 x_K y_K 512 p q

lemma evalBivK5_bivSub (p q : Biv) : evalBivK5 (bivSub p q) = evalBivK5 p - evalBivK5 q := by
  rw [bivSub, evalBivK5, merge_denote, negBiv_denote, ← sub_eq_add_neg]; rfl

lemma evalBivK5_bivMul (p q : Biv) : evalBivK5 (bivMul p q) = evalBivK5 p * evalBivK5 q :=
  multiply_denote vK5 x_K y_K p q

lemma evalBivK5_bivScale (c : ℤ) (p : Biv) : evalBivK5 (bivScale c p) = (c : K5) * evalBivK5 p := by
  rw [bivScale, evalBivK5, scale_denote]; simp [ringEval, evalBivK5]


end SymmetricSexticResidual.LocalResidueU0


