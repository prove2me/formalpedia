-- Prove2me | Definitions.Def_MazurTransfer_Order18SelectedLocalProjectionData
-- name    : MazurTransfer_Order18SelectedLocalProjectionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T18:05:56.323047+00:00
-- url     : https://prove2.me/theorems/ea2ca99e-b9cf-4216-aaae-870ec572df10
-- title:
--   Order18: the certified selected local root and its squareclass projection
-- statement:
--   In the published coefficient-field completion, this package chooses the root \(\rho\) of \(S^3-3S-10\) in the maximal ideal from the separately Proved Hensel-root existence theorem. It defines the original algebra projection \(M\to\widehat K\), the induced map on unit square classes, and the two explicit affine root transforms used by the quotient and minimal models. The root specifications and polynomial-vanishing witness are essential parts of constructing the algebra map. Point-image triviality and separation of the sixteen kernel representatives are separate arithmetic theorems.
-- source:
--   Exact original root, algebra projection, induced squareclass map and affine-root definitions from user WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, selected by typed kernel dependencies and whole original Lean AST ownership. The existence proof is supplied by the separately Proved public Hensel certificate; proof irrelevance preserves the exact original chosen-root value. Only pure data and essential constructor/specification witnesses are retained. Original Apache-2.0 headers and attribution are preserved. Named downstream consumers: separate original local point-image triviality and representative-separation proofs, then the unchanged order18 local mask exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order18CoefficientCompletionData
import Definitions.Def_MazurTransfer_Order18AmbientSelmer
import Definitions.Def_MazurTransfer_Order18MinimalHalvingData
import Theorems.Thm_MazurTransfer_order18_coefficient_hensel_root_exists

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
private theorem exists_localTwoDivisionRoot_aux :
    ∃ r : CoefficientCompletionIntegers,
      localTwoDivisionPolynomial.IsRoot r ∧
        r ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers :=
  MazurTransfer.order18_coefficient_hensel_root_exists
end MazurTorsion.XOneEighteenDyadicCompletionBridge


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionArithmetic. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Exact arithmetic for the `X₁(18)` two-division algebra

This file records the exact algebraic-number certificates used by the
two-descent on the real-cubic elliptic quotient.  The rational cubic

`S³ - 3S - 10`

is proved irreducible by reduction modulo `11`.  We then form its relative
base change to the real cubic field `K = ℚ(τ)`.  All displayed relative
norm identities are checked in the kernel by the resultant formula for a
monogenic cubic algebra.

The relative object is deliberately called an algebra here: its field
structure is supplied only after a separate primitive-element certificate
proves that the two cubic fields are linearly disjoint.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

namespace Q







end Q



/-! ## The rational two-division cubic -/







































/-! ## The relative cubic algebra over the quotient field -/

























/-! ## Exact relative norm certificates -/

























end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


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



/-! ## The actual dyadic prime of the coefficient field -/























/-! ## Quotients commute with adic completion -/

section CompletionQuotient

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]











end CompletionQuotient

/-! ## The coefficient completion modulo `2⁷` -/

open MazurTorsion.XOneEighteenDyadicLocalImage























































/-! ## The selected simple root of the local two-division cubic -/

















/-- The Hensel lift of the simple root `0` modulo the dyadic maximal
ideal. -/
noncomputable def localTwoDivisionRoot : CoefficientCompletionIntegers :=
  Classical.choose exists_localTwoDivisionRoot_aux

theorem localTwoDivisionRoot_isRoot :
    localTwoDivisionPolynomial.IsRoot localTwoDivisionRoot :=
  (Classical.choose_spec exists_localTwoDivisionRoot_aux).1

theorem localTwoDivisionRoot_mem_maximalIdeal :
    localTwoDivisionRoot ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers :=
  (Classical.choose_spec exists_localTwoDivisionRoot_aux).2















/-! ## The unramified dyadic uniformizer and square lifting -/













/-! ## The normalized projected curve over the integer ring -/



























/-! ## Passage to the completion field -/























/-! ## Projection of the genuine relative descent algebra -/

private theorem localTwoDivisionRoot_cubic_field :
    (localTwoDivisionRoot : CoefficientCompletion) ^ 3 -
        3 * localTwoDivisionRoot - 10 = 0 := by
  have hroot : localTwoDivisionRoot ^ 3 -
      3 * localTwoDivisionRoot - 10 = 0 := by
    simpa only [Polynomial.IsRoot, localTwoDivisionPolynomial,
      eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat] using
      localTwoDivisionRoot_isRoot
  exact congrArg Subtype.val hroot

/-- Evaluation at the selected Hensel root is the actual `K`-algebra
projection from the relative cubic two-division field to the chosen
coefficient-field completion. -/
noncomputable def localRelativeProjection :
    M →ₐ[Q.K] CoefficientCompletion :=
  AdjoinRoot.liftAlgHom relativePolynomial
    (Algebra.ofId Q.K CoefficientCompletion)
    (localTwoDivisionRoot : CoefficientCompletion) (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      simp only [relativePolynomial, map_sub, map_pow, aeval_X,
        map_mul, map_ofNat]
      exact localTwoDivisionRoot_cubic_field)



/-- The selected root of the rational-coefficient descent cubic in the
coefficient completion. -/
def localProjectedDescentRoot : CoefficientCompletion :=
  (3 * (localTwoDivisionRoot : CoefficientCompletion) ^ 2 -
      6 * localTwoDivisionRoot - 5) / 4











/-- The corresponding selected root on the minimal dyadic-support model. -/
def localProjectedMinimalRoot : CoefficientCompletion :=
  (localProjectedDescentRoot -
      algebraMap Q.K CoefficientCompletion rationalAbscissaTranslation) / 9



/-! ## The selected factor of the base-changed minimal descent algebra -/











/-! ## The local image of the minimal descent map -/





























/-- Square-class projection directly from the explicit degree-nine
compositum to the selected dyadic factor. -/
noncomputable def localRelativeSquareclassProjection :
    Units.modPow M 2 →* Units.modPow CoefficientCompletion 2 :=
  Units.modPow.map localRelativeProjection.toMonoidHom 2









end

end MazurTorsion.XOneEighteenDyadicCompletionBridge

end


