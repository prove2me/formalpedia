-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c17
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c17
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-09T02:22:26.279149+00:00
-- url     : https://prove2.me/theorems/9f98933b-f5ef-41ca-ba3f-4460055b1258
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate source foundation (consolidated part 3 of 9)
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate

import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c12
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
Source pin: b07243d72093bec5686e15b1208cb50d000f3e8d.
Source-only repair of the certificate candidate from
4109ba77745784c1a9f8c4c7b304df4124bf5ac4. Lean and axiom checks NOT RUN.

Finite polynomial certificates for all 32 * 4 coefficient pairs in the
GOOD F2 model. Polynomial divisibility is never passed to a decision
procedure. The six local equations have explicit cofactors. Each of the
58 unsupported nonzero norms has an explicit factor coprime to both X
and X - 1; its two Bezout identities rule out support. The zero norm is
excluded separately. The 69 supported rows have explicit six-polynomial
normal forms and first-nonzero-coefficient certificates.

All public definition values and theorem statements are unchanged.
The link between these nine-jet orders and the six geometric local
orders is a separate theorem.
-/

namespace MazurProof.N13SpecialSmallFunctionCertificate

noncomputable section
open Polynomial

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
theorem row_8_2 : PairCertificate ![0, 0, 0, 1, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 0] ![0, 1] =
    ![X ^ 3 + X ^ 5 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 1, 0, 1, 3, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (8, 3).
theorem row_8_3 : PairCertificate ![0, 0, 0, 1, 0] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 0, 1, 0]) (ordinate ![1, 1]) := by
    refine ⟨X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - 2 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (9, 0).
theorem row_9_0 : PairCertificate ![1, 0, 0, 1, 0] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 1, 0]) (ordinate ![0, 0]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 2 + X ^ 3 - X ^ 4) * two_poly
  exact False.elim (obstruction_21 (hf.trans h))

-- Coefficient bit codes (a, b) = (9, 1).
theorem row_9_1 : PairCertificate ![1, 0, 0, 1, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 0, 1, 0] ![1, 0] =
    ![1 + X ^ 3 + X ^ 4 + X ^ 7,
      X + X ^ 4 + X ^ 7,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 2 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 1, 4, 0, 1, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (9, 2).
theorem row_9_2 : PairCertificate ![1, 0, 0, 1, 0] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 1, 0]) (ordinate ![0, 1]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 4 - X ^ 5 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (9, 3).
theorem row_9_3 : PairCertificate ![1, 0, 0, 1, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 0, 1, 0] ![1, 1] =
    ![1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 2 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 2, 1, 3, 2, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (10, 0).
theorem row_10_0 : PairCertificate ![0, 1, 0, 1, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 1, 0] ![0, 0] =
    ![X + X ^ 3,
      X + X ^ 3,
      X ^ 2 + X ^ 3,
      X ^ 2 + X ^ 3,
      X + X ^ 3,
      X + X ^ 3] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 1, 2, 2, 1, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (10, 1).
theorem row_10_1 : PairCertificate ![0, 1, 0, 1, 0] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 0, 1, 0]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 4 - X ^ 5) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (10, 2).
theorem row_10_2 : PairCertificate ![0, 1, 0, 1, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 1, 0] ![0, 1] =
    ![X + X ^ 3 + X ^ 5 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 2 * X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 2, 1, 0, 4, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (10, 3).
theorem row_10_3 : PairCertificate ![0, 1, 0, 1, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 1, 0] ![1, 1] =
    ![X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X + X ^ 2 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 4, 1, 2, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (11, 0).
theorem row_11_0 : PairCertificate ![1, 1, 0, 1, 0] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 0, 1, 0]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 3 + X ^ 4) * two_poly
  exact False.elim (obstruction_69 (hf.trans h))

-- Coefficient bit codes (a, b) = (11, 1).
end
end MazurProof.N13SpecialSmallFunctionCertificate


