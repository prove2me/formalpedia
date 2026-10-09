-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c03
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c03
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-09T01:29:57.400748+00:00
-- url     : https://prove2.me/theorems/e1c01e65-a658-48fc-872c-0518b3275009
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate source foundation (part 3 of 50)
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate

import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c02
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
theorem obstruction_81 :
    ¬ (1 + X ^ 4 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X ^ 3 + X ^ 5) (X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 4 + X ^ 6) * two_poly
  · linear_combination (X ^ 6) * two_poly

theorem obstruction_91 :
    ¬ (1 + X + X ^ 3 + X ^ 4 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X ^ 2 + X ^ 3 + X ^ 5) (X + X ^ 2 + X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 3 + X ^ 4 + X ^ 6) * two_poly
  · linear_combination (X ^ 3 + X ^ 6) * two_poly

theorem obstruction_103 :
    ¬ (1 + X + X ^ 2 + X ^ 5 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X + X ^ 4 + X ^ 5) (X + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
  · linear_combination (X ^ 2 + X ^ 6) * two_poly

theorem obstruction_109 :
    ¬ (1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 2 + X ^ 4 + X ^ 5) (X ^ 2 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  · linear_combination (X ^ 3 + X ^ 6) * two_poly

theorem obstruction_117 :
    ¬ (1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 3 + X ^ 4 + X ^ 5) (X ^ 2 + X ^ 3 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  · linear_combination (X ^ 4 + X ^ 6) * two_poly

theorem obstruction_261 :
    ¬ (1 + X ^ 2 + X ^ 8 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 7) (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 8) * two_poly
  · linear_combination (X ^ 8) * two_poly

theorem obstruction_273 :
    ¬ (1 + X ^ 4 + X ^ 8 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X ^ 3 + X ^ 7) (X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 4 + X ^ 8) * two_poly
  · linear_combination (X ^ 8) * two_poly

theorem obstruction_321 :
    ¬ (1 + X ^ 6 + X ^ 8 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X ^ 5 + X ^ 7) (X ^ 6 + X ^ 7)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 6 + X ^ 8) * two_poly
  · linear_combination (X ^ 8) * two_poly

theorem obstruction_341 :
    ¬ (1 + X ^ 2 + X ^ 4 + X ^ 6 + X ^ 8 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 3 + X ^ 5 + X ^ 7) (X ^ 2 + X ^ 3 + X ^ 6 + X ^ 7)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 4 + X ^ 6 + X ^ 8) * two_poly
  · linear_combination (X ^ 4 + X ^ 8) * two_poly

-- Coefficient bit codes (a, b) = (0, 0).
theorem row_0_0 : PairCertificate ![0, 0, 0, 0, 0] ![0, 0] := by
  intro h
  have hn : N13SpecialAffineNorm.normPolynomial
      (numerator ![0, 0, 0, 0, 0]) (ordinate ![0, 0]) = 0 := by
    simp [N13SpecialAffineNorm.normPolynomial, numerator, ordinate, Fin.sum_univ_succ]
  rw [hn, zero_dvd_iff] at h
  have hx1 : (X : K[X]) - 1 ≠ 0 := by
    simpa using (Polynomial.X_sub_C_ne_zero (1 : K))
  exact False.elim ((mul_ne_zero (pow_ne_zero 16 Polynomial.X_ne_zero)
    (pow_ne_zero 16 hx1)) h)

-- Coefficient bit codes (a, b) = (0, 1).
end
end MazurProof.N13SpecialSmallFunctionCertificate


