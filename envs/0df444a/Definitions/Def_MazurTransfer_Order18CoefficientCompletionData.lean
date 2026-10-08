-- Prove2me | Definitions.Def_MazurTransfer_Order18CoefficientCompletionData
-- name    : MazurTransfer_Order18CoefficientCompletionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T17:43:16.062812+00:00
-- url     : https://prove2.me/theorems/6278ea64-ec4a-489e-973b-7969d56731b3
-- title:
--   Order18: the exact coefficient-field dyadic completion and local cubic
-- statement:
--   This package defines the original Kummer–Dedekind prime above \(2\) in the full ring of integers of \(K=\mathbb Q[T]/(T^3-3T-1)\), its coefficient-field completion and completion-integer ring, and the local polynomial \(S^3-3S-10\). The separately Proved coefficient-prime certificate supplies the exact prerequisites of the prime constructor. The selected cubic root and all local-solubility and descent conclusions remain separate arithmetic obligations.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Seven original reachable declarations selected by typed kernel dependencies and complete original Lean AST ranges. Pure prime/completion/polynomial definitions and the essential constructor membership witness are retained. The two arithmetic prerequisites are supplied by the separately Proved coefficient dyadic-prime certificate. Original canonical prime construction, coefficient field, Apache-2.0 headers and attribution preserved. Named downstream consumer: the selected Hensel root existence certificate and the unchanged order18 local descent exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order18MinimalHalvingData
import Definitions.Def_MazurTransfer_Order18CoefficientIntegerData
import Theorems.Thm_MazurTransfer_order18_coefficient_dyadic_prime_certificate

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralElements
end MazurTorsion.XOneEighteenTwoDivisionIntegralElements

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralModel
end MazurTorsion.XOneEighteenTwoDivisionIntegralModel

namespace MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
end MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicLift
end MazurTorsion.XOneEighteenTwoDivisionTriadicLift

namespace MazurTorsion.XOneEighteenDyadicLocalImage
end MazurTorsion.XOneEighteenDyadicLocalImage

namespace MazurTorsion.XOneEighteenDyadicCompletionBridge
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
private theorem coefficient_not_dvd_exponent_two :
    ¬ 2 ∣ _root_.RingOfIntegers.exponent coefficientInteger :=
  MazurTransfer.order18_coefficient_dyadic_prime_certificate.1
private theorem coefficientPolynomialInt_mem_monicFactors_two :
    coefficientPolynomialInt.map (Int.castRingHom (ZMod 2)) ∈
      _root_.RingOfIntegers.monicFactorsMod coefficientInteger 2 :=
  MazurTransfer.order18_coefficient_dyadic_prime_certificate.2
end MazurTorsion.XOneEighteenDyadicCompletionBridge


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDyadicCompletionBridge. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The dyadic completion behind the `X₁(18)` local certificate

The finite calculation in `XOneEighteenDyadicLocalImage` takes place in the
unramified cubic ring modulo `2⁷`.  This file begins the arithmetic bridge
to that ring.  It constructs the actual prime above `2` in the full ring of
integers of the real cubic coefficient field and proves, at arbitrary
precision, that quotienting before or after adic completion gives the same
ring.

No conclusion about the local descent image is drawn merely from this
higher-residue comparison.  The remaining bridge must still identify the
chosen polynomial presentation modulo `2⁷`, lift the selected simple root
of the two-division cubic, and treat both integral and nonintegral local
points.
-/

open Polynomial IsDedekindDomain WithZero WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenDyadicCompletionBridge

noncomputable section

open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid
open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionTriadicLift

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! ## The actual dyadic prime of the coefficient field -/







/-- The Kummer--Dedekind prime selected by the irreducible cubic factor
modulo `2`. -/
def coefficientPrimeTwoIdeal : Ideal (𝓞 Q.K) :=
  (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      coefficient_not_dvd_exponent_two).symm
    ⟨coefficientPolynomialInt.map (Int.castRingHom (ZMod 2)),
      coefficientPolynomialInt_mem_monicFactors_two⟩

theorem coefficientPrimeTwo_mem_primesOver :
    coefficientPrimeTwoIdeal ∈
      Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 Q.K) :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      coefficient_not_dvd_exponent_two).symm
    ⟨coefficientPolynomialInt.map (Int.castRingHom (ZMod 2)),
      coefficientPolynomialInt_mem_monicFactors_two⟩).property





/-- The unique height-one prime represented by the irreducible factor of
the coefficient polynomial modulo `2`. -/
def coefficientPrimeTwo : HeightOneSpectrum (𝓞 Q.K) :=
  .ofPrime (Ideal.prime_of_mem_primesOver
    (by norm_num) coefficientPrimeTwo_mem_primesOver)







/-! ## Quotients commute with adic completion -/

section CompletionQuotient

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]











end CompletionQuotient

/-! ## The coefficient completion modulo `2⁷` -/

open MazurTorsion.XOneEighteenDyadicLocalImage























































/-! ## The selected simple root of the local two-division cubic -/

abbrev CoefficientCompletionIntegers :=
  coefficientPrimeTwo.adicCompletionIntegers Q.K

/-- The two-division cubic over the integers of the coefficient
completion. -/
def localTwoDivisionPolynomial : Polynomial CoefficientCompletionIntegers :=
  X ^ 3 - 3 * X - 10

































/-! ## The unramified dyadic uniformizer and square lifting -/













/-! ## The normalized projected curve over the integer ring -/



























/-! ## Passage to the completion field -/

/-- The selected dyadic completion of the coefficient field. -/
abbrev CoefficientCompletion := coefficientPrimeTwo.adicCompletion Q.K





















/-! ## Projection of the genuine relative descent algebra -/























/-! ## The selected factor of the base-changed minimal descent algebra -/











/-! ## The local image of the minimal descent map -/







































end

end MazurTorsion.XOneEighteenDyadicCompletionBridge

end


