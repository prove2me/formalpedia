-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c37
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c37
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-09T02:47:07.363647+00:00
-- url     : https://prove2.me/theorems/9c6abcd2-18e2-498e-8a7a-cb2fae05e21d
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate source foundation (consolidated part 7 of 9)
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate

import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c17
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
theorem row_20_1 : PairCertificate ![0, 0, 1, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 1, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X ^ 2 + X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 2 - X ^ 3 - X ^ 4 - 2 * X ^ 5 + X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_37 (hf.trans h))

-- Coefficient bit codes (a, b) = (20, 2).
theorem row_20_2 : PairCertificate ![0, 0, 1, 0, 1] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 1, 0, 1]) (ordinate ![0, 1]) := by
    refine ⟨X ^ 3 + X ^ 4, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - X ^ 4 - X ^ 5 - X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (20, 3).
theorem row_20_3 : PairCertificate ![0, 0, 1, 0, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 0, 1] ![1, 1] =
    ![X ^ 2 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 0, 3, 1, 0, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (21, 0).
theorem row_21_0 : PairCertificate ![1, 0, 1, 0, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 4 + X ^ 8 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 0, 1]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 2 + X ^ 4 + X ^ 6) * two_poly
  exact False.elim (obstruction_273 (hf.trans h))

-- Coefficient bit codes (a, b) = (21, 1).
theorem row_21_1 : PairCertificate ![1, 0, 1, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 3 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 3 - 2 * X ^ 5 + X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_73 (hf.trans h))

-- Coefficient bit codes (a, b) = (21, 2).
theorem row_21_2 : PairCertificate ![1, 0, 1, 0, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 0, 1] ![0, 1] =
    ![1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 8,
      1 + X + X ^ 5 + X ^ 8,
      1 + X + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 5 + X ^ 6 + X ^ 8] := by
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
        linear_combination (X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X ^ 2 + X ^ 4) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 0, 7, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (21, 3).
theorem row_21_3 : PairCertificate ![1, 0, 1, 0, 1] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 0, 1]) (ordinate ![1, 1]) := by
    refine ⟨X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - 2 * X ^ 3 - X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (22, 0).
theorem row_22_0 : PairCertificate ![0, 1, 1, 0, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 0, 1]) (ordinate ![0, 0]) := by
    refine ⟨X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  exact False.elim (obstruction_69 (hf.trans h))

-- Coefficient bit codes (a, b) = (22, 1).
theorem row_22_1 : PairCertificate ![0, 1, 1, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - 2 * X ^ 4 - X ^ 5 - X ^ 7) * two_poly
  exact False.elim (obstruction_59 (hf.trans h))

-- Coefficient bit codes (a, b) = (22, 2).
theorem row_22_2 : PairCertificate ![0, 1, 1, 0, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 1] ![0, 1] =
    ![X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 5 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
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
        linear_combination (X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 5, 0, 1, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (22, 3).
theorem row_22_3 : PairCertificate ![0, 1, 1, 0, 1] ![1, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 0, 1]) (ordinate ![1, 1]) := by
    refine ⟨X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - 2 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_61 (hf.trans h))

-- Coefficient bit codes (a, b) = (23, 0).
theorem row_23_0 : PairCertificate ![1, 1, 1, 0, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 4 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 1]) (ordinate ![0, 0]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5) * two_poly
  exact False.elim (obstruction_81 (hf.trans h))

-- Coefficient bit codes (a, b) = (23, 1).
theorem row_23_1 : PairCertificate ![1, 1, 1, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - X ^ 4 - 2 * X ^ 5 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (23, 2).
theorem row_23_2 : PairCertificate ![1, 1, 1, 0, 1] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 1]) (ordinate ![0, 1]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - X ^ 5 - X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_59 (hf.trans h))

-- Coefficient bit codes (a, b) = (23, 3).
theorem row_23_3 : PairCertificate ![1, 1, 1, 0, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 1, 0, 1] ![1, 1] =
    ![1 + X + X ^ 2 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (3 + 5 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 1, 1, 4, 0, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (24, 0).
theorem row_24_0 : PairCertificate ![0, 0, 0, 1, 1] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 1] ![0, 0] =
    ![X ^ 3 + X ^ 4,
      X ^ 3 + X ^ 4,
      X + X ^ 2 + X ^ 3 + X ^ 4,
      X + X ^ 2 + X ^ 3 + X ^ 4,
      1 + X,
      1 + X] := by
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
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 2 * X ^ 3) * two_poly
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
  apply goodJets_of_coefficients _ ![3, 3, 1, 1, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (24, 1).
theorem row_24_1 : PairCertificate ![0, 0, 0, 1, 1] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 1] ![1, 0] =
    ![X ^ 3 + X ^ 7,
      1 + X + X ^ 7,
      X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4) * two_poly
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
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 0, 5, 0, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (24, 2).
theorem row_24_2 : PairCertificate ![0, 0, 0, 1, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 1] ![0, 1] =
    ![X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
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
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 1, 2, 0, 0, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (24, 3).
end
end MazurProof.N13SpecialSmallFunctionCertificate


