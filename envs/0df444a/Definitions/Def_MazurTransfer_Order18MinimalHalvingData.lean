-- Prove2me | Definitions.Def_MazurTransfer_Order18MinimalHalvingData
-- name    : MazurTransfer_Order18MinimalHalvingData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T16:43:38.402955+00:00
-- url     : https://prove2.me/theorems/384b28c7-2031-42ea-8bca-796e233ded6e
-- title:
--   Order18: the exact minimal completed-square model and its compositum root
-- statement:
--   Let \(K=\mathbb{Q}[T]/(T^3-3T-1)\) and \(M=K[S]/(S^3-3S-10)\). This package defines the original completed-square elliptic model over \(K\) and its explicit cubic root \(\eta\in M\). The curve is obtained from the published quotient by completing the square; the root is the original affine transform of the published relative cubic generator. These are pure data. Point divisibility and all descent conclusions are separate theorem obligations.
-- source:
--   Exact original minimal curve, coefficient-field aliases and explicit cubic-root definitions from user WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, selected by typed declaration ownership and complete original Lean AST command ranges. Original copyright, author list and Apache-2.0 header retained. The six retained declarations are pure definitions over the already published original coefficient and relative field data. Divisibility and all global/local arithmetic remain separate theorems. Named downstream consumer: the unchanged unconditional original cubic quotient doubling-surjectivity theorem, MazurTransfer.order18_original_quotient_doubling_surjective.

import Mathlib
import Definitions.Def_MazurTransfer_Order18AmbientSelmer
namespace MazurTorsion.XOneEighteenTwoDivisionClassNumber
end MazurTorsion.XOneEighteenTwoDivisionClassNumber
namespace MazurTorsion.XOneEighteenQuotientRankZero
end MazurTorsion.XOneEighteenQuotientRankZero
namespace MazurTorsion.XOneEighteenTwoDivisionIntegralModel
end MazurTorsion.XOneEighteenTwoDivisionIntegralModel


/- Source module: MazurTorsion.NumberTheory.XOneEighteenQuotientTwoDescentModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# A characteristic-not-two model of the `X₁(18)` elliptic quotient

This file puts the real-cubic elliptic quotient into the form used by the
`x-T` two-descent.  Both coordinate changes are genuine admissible changes
of Weierstrass variables, so the resulting point maps are additive
equivalences rather than equation-only substitutions.

The completed two-division cubic is also identified with the explicit
relative cubic algebra used by the arithmetic certificates.  No
Mordell--Weil or Selmer conclusion is asserted here.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientTwoDescentModel

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenTwoDivisionArithmetic

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K







/-! ## Admissible point-group equivalences -/





















/-! ## The completed two-division cubic -/



/-- The explicit element of the relative cubic algebra corresponding to a
two-division abscissa. -/
def descentRootInM : M :=
  algebraMap K M (1 / 4 : K) * relativeTwoDivisionZ



end

end MazurTorsion.XOneEighteenQuotientTwoDescentModel

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenMinimalTwoDescentModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# A dyadic-support two-descent model for the `X₁(18)` quotient

The rational-coefficient model used for explicit two-division arithmetic is
obtained from the original real-cubic quotient by a change with scale `3`.
It is consequently nonminimal at the primes above `3`.  For the global
Selmer containment we instead complete the square directly on the original
quotient, whose discriminant is `-2`.

The abscissas on the two completed-square models are related by

`z = 9 w + 3τ² + 3τ - 8`.

Thus the new cubic algebra is the same explicit degree-nine compositum, but
its bad-prime support is genuinely dyadic.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenMinimalTwoDescentModel

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenDescentAlgebraEquiv

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K



/-- The completed-square model of the original discriminant-`-2` quotient. -/
def minimalDescentCurve : WeierstrassCurve K :=
  quotientCurve.toCharNeTwoNF • quotientCurve













/-- Translation term in the scale-three change from the original quotient
to the rational-coefficient model. -/
def rationalAbscissaTranslation : K :=
  3 * tau ^ 2 + 3 * tau - 8

/-- The root of the minimal cubic in the explicit compositum. -/
def minimalDescentRootInM : M :=
  (descentRootInM - algebraMap K M rationalAbscissaTranslation) / 9



























end

end MazurTorsion.XOneEighteenMinimalTwoDescentModel

end


