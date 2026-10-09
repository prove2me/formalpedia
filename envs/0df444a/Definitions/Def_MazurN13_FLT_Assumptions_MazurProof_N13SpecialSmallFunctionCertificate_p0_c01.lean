-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c01
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c01
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-09T01:07:08.011984+00:00
-- url     : https://prove2.me/theorems/884fd27f-e8f2-4377-9eb4-0a22c5fad210
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate source foundation (part 1 of 50)
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate

import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallNumerator_p0
import Mathlib.RingTheory.Coprime.Lemmas
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

abbrev K := N13GoodModelTwo.F2

def numerator (a : Fin 5 → K) : K[X] := ∑ i : Fin 5, C (a i) * X ^ (i : ℕ)
def ordinate (b : Fin 2 → K) : K[X] := C (b 0) + C (b 1) * X

def jetZeroZero : K[X] := X ^ 4 + X ^ 7
def jetZeroOne : K[X] := 1 + X + X ^ 3 + X ^ 4 + X ^ 7
def jetOneZero : K[X] := X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8
def jetOneOne : K[X] := 1 + X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8
def jetInfinityZero : K[X] := X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8
def jetInfinityOne : K[X] := 1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8

def residual (H R s : K[X]) : K[X] := s ^ 2 + H * s - R

theorem two_poly : (2 : K[X]) = 0 :=
  CharP.cast_eq_zero (K[X]) 2

/-- The displayed polynomials really satisfy all six local equations to
nine-jet precision. The divisibility witnesses are explicit polynomials. -/
theorem jet_polynomials_satisfy_equations :
    (X : K[X]) ^ 9 ∣ residual N13GoodCoordinateRingTwo.hPoly N13GoodCoordinateRingTwo.rhsPoly jetZeroZero ∧
    (X : K[X]) ^ 9 ∣ residual N13GoodCoordinateRingTwo.hPoly N13GoodCoordinateRingTwo.rhsPoly jetZeroOne ∧
    (X : K[X]) ^ 9 ∣ residual (N13GoodCoordinateRingTwo.hPoly.comp (X + 1))
      (N13GoodCoordinateRingTwo.rhsPoly.comp (X + 1)) jetOneZero ∧
    (X : K[X]) ^ 9 ∣ residual (N13GoodCoordinateRingTwo.hPoly.comp (X + 1))
      (N13GoodCoordinateRingTwo.rhsPoly.comp (X + 1)) jetOneOne ∧
    (X : K[X]) ^ 9 ∣ residual N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly jetInfinityZero ∧
    (X : K[X]) ^ 9 ∣ residual N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly jetInfinityOne := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨X + X ^ 5, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (X ^ 7 + X ^ 8 + X ^ 11) * two_poly
  · refine ⟨X + X ^ 5, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (1 + 2 * X + X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + X ^ 5 + X ^ 6 + 3 * X ^ 7 + 2 * X ^ 8 + X ^ 10 + X ^ 11) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (-1 - 3 * X - 4 * X ^ 2 - X ^ 3 + 4 * X ^ 4 + 7 * X ^ 5 + 8 * X ^ 6 + 7 * X ^ 7 + 6 * X ^ 8 + 5 * X ^ 9 + 4 * X ^ 10 + 2 * X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (1 - 4 * X ^ 2 - 5 * X ^ 3 + 5 * X ^ 5 + 7 * X ^ 6 + 5 * X ^ 7 + 5 * X ^ 8 + 4 * X ^ 9 + 3 * X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6 + 3 * X ^ 7 + 3 * X ^ 8 + 3 * X ^ 9 + 2 * X ^ 10 + 2 * X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (1 + X + 2 * X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + 3 * X ^ 5 + 4 * X ^ 6 + 3 * X ^ 7 + 4 * X ^ 8 + 2 * X ^ 9 + 3 * X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly

/-- First nonzero coefficient among 0,...,8; value9 means no such coefficient. -/
def jetOrder (p : K[X]) : ℕ :=
  (List.range 9).findIdx (fun n => decide (p.coeff n ≠ 0))

def infinityNumerator (a : Fin 5 → K) : K[X] := ∑ i : Fin 5, C (a i) * X ^ (4 - (i : ℕ))
def infinityOrdinate (b : Fin 2 → K) : K[X] := C (b 0) * X + C (b 1)

def sixJetPolynomials (a : Fin 5 → K) (b : Fin 2 → K) : Fin 6 → K[X] := ![
  numerator a + ordinate b * jetZeroZero,
  numerator a + ordinate b * jetZeroOne,
  (numerator a).comp (X + 1) + (ordinate b).comp (X + 1) * jetOneZero,
  (numerator a).comp (X + 1) + (ordinate b).comp (X + 1) * jetOneOne,
  infinityNumerator a + infinityOrdinate b * jetInfinityZero,
  infinityNumerator a + infinityOrdinate b * jetInfinityOne]

def sixJetOrders (a : Fin 5 → K) (b : Fin 2 → K) (i : Fin 6) : ℕ :=
  jetOrder (sixJetPolynomials a b i)

end
end MazurProof.N13SpecialSmallFunctionCertificate


