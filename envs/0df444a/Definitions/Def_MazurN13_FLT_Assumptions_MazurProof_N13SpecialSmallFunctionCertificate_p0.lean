-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-09T03:15:15.299534+00:00
-- url     : https://prove2.me/theorems/e3a95586-4743-4710-a59c-57119f4911a0
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate source foundation (consolidated part 9 of 9)
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate

import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c22
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c27
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c32
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c37
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c42
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
theorem row_29_2 : PairCertificate ![1, 0, 1, 1, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 1, 1] ![0, 1] =
    ![1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      1 + X + X ^ 3 + X ^ 5 + X ^ 8,
      X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 5 + X ^ 6 + X ^ 8] := by
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
        linear_combination (2 + 5 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 4) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 3, 0, 0, 5]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (29, 3).
theorem row_29_3 : PairCertificate ![1, 0, 1, 1, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 1, 1] ![1, 1] =
    ![1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 2 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9] := by
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
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 6 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (3 + 6 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 4, 1, 2, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (30, 0).
theorem row_30_0 : PairCertificate ![0, 1, 1, 1, 1] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 1, 1] ![0, 0] =
    ![X + X ^ 2 + X ^ 3 + X ^ 4,
      X + X ^ 2 + X ^ 3 + X ^ 4,
      X ^ 3 + X ^ 4,
      X ^ 3 + X ^ 4,
      1 + X + X ^ 2 + X ^ 3,
      1 + X + X ^ 2 + X ^ 3] := by
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
        linear_combination (2 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3) * two_poly
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
  apply goodJets_of_coefficients _ ![1, 1, 3, 3, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (30, 1).
theorem row_30_1 : PairCertificate ![0, 1, 1, 1, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 3 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 1, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 4 + X ^ 6) * two_poly
  exact False.elim (obstruction_73 (hf.trans h))

-- Coefficient bit codes (a, b) = (30, 2).
theorem row_30_2 : PairCertificate ![0, 1, 1, 1, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 1, 1] ![0, 1] =
    ![X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 3 + X ^ 5 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
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
        linear_combination (2 + 5 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 6 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 3, 1, 0, 0, 3]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (30, 3).
theorem row_30_3 : PairCertificate ![0, 1, 1, 1, 1] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 1, 1]) (ordinate ![1, 1]) := by
    refine ⟨X + X ^ 2 + X ^ 3 + X ^ 4, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - 2 * X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (31, 0).
theorem row_31_0 : PairCertificate ![1, 1, 1, 1, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 + X ^ 6 + X ^ 8 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 1, 1]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + X ^ 6 + X ^ 7) * two_poly
  exact False.elim (obstruction_341 (hf.trans h))

-- Coefficient bit codes (a, b) = (31, 1).
theorem row_31_1 : PairCertificate ![1, 1, 1, 1, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 1, 1]) (ordinate ![1, 0]) := by
    refine ⟨X ^ 2 + X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 6) * two_poly
  exact False.elim (obstruction_37 (hf.trans h))

-- Coefficient bit codes (a, b) = (31, 2).
theorem row_31_2 : PairCertificate ![1, 1, 1, 1, 1] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 1, 1]) (ordinate ![0, 1]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 4) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (31, 3).
theorem row_31_3 : PairCertificate ![1, 1, 1, 1, 1] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 2 + X ^ 5 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 1, 1]) (ordinate ![1, 1]) := by
    refine ⟨X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_103 (hf.trans h))

theorem binary (x : K) : x = 0 ∨ x = 1 := by
  revert x; decide

/-- The norm-support restriction leaves only genuine nonzero nine-jets,
and every surviving pair has zero weighted code. The common infinity
shift -4 cancels between the last two coefficients, whose weights sum to 0. -/
theorem supported_small_function_certificate :
    ∀ (a : Fin 5 → K) (b : Fin 2 → K),
      N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
          (X : K[X]) ^ 16 * (X - 1) ^ 16 →
        (∀ i : Fin 6, sixJetOrders a b i < 9 ∧
          (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
          ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0) ∧
        weightedJetCode a b = 0 := by
  intro a b
  change PairCertificate a b
  have ha : a = ![a 0, a 1, a 2, a 3, a 4] := by
    funext i
    fin_cases i <;> rfl
  have hb : b = ![b 0, b 1] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, hb]
  rcases binary (a 0) with h0 | h0 <;>
    rcases binary (a 1) with h1 | h1 <;>
    rcases binary (a 2) with h2 | h2 <;>
    rcases binary (a 3) with h3 | h3 <;>
    rcases binary (a 4) with h4 | h4 <;>
    rcases binary (b 0) with k0 | k0 <;>
    rcases binary (b 1) with k1 | k1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_3

end
end MazurProof.N13SpecialSmallFunctionCertificate


