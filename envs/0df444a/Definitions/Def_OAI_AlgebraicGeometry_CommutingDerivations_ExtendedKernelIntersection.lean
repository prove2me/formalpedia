-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedKernelIntersection
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_ExtendedKernelIntersection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:39:27.416988+00:00
-- url     : https://prove2.me/theorems/bcbff547-8115-40b3-bd21-655a45817152
-- title:
--   The extended Laurent coefficient map fixes complex constants
-- statement:
--   Let $R=\mathbb{C}[h,u,v,w]$, let $R_{F+1}$ be its localization away from $F+1$, where $F$ is the polynomial of the construction, and let $\Lambda=\mathbb{C}[c,c^{-1}]$ be the Laurent polynomial ring with the coefficient map $\kappa:\Lambda\to R_{F+1}$, $c\mapsto F+1$. For a natural number $n$ let $E_n=R_{F+1}[Z_0,\dots,Z_{n-5}]$ be the polynomial ring in $n-4$ variables over $R_{F+1}$, and let $\kappa_n:\Lambda\to E_n$ send $a$ to the constant polynomial $\kappa(a)$. The file records a single evaluation lemma: for every $n$ and every $a\in\mathbb{C}$,
--
--   $$
--   \kappa_n(a)=a\qquad\text{in }E_n,
--   $$
--
--   that is, the complex constants of $\Lambda$ go to the complex constants of $E_n$.
--
--   This is the compatibility of the extended coefficient map with the complex scalars. It belongs to the comparison between Laurent coefficients and polynomials in $F_n$ (the copy of $F$ in the first four of $n$ variables) by which, in every dimension $n\ge4$, the elements of $\mathbb{C}[X_0,\dots,X_{n-1}]$ whose localized image has constant coordinates over $\Lambda$ are identified with $\mathbb{C}[F_n]$.
--
--   **Formalization Note** The lemma is `extendedCoefficientMap_complex`. It holds for every natural number $n$ with no hypothesis $4\le n$; here $n-4$ is natural-number subtraction, so for $n<4$ the ring $E_n$ has no variables.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedKernelIntersection.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedKernelIntersection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CommutingDerivations mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBezout
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationSetup
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_CoefficientInstances
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBridge
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationEquivalence
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedLocalization
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ConcreteKernelIntersection

namespace OAI

/-!
The coefficient algebra of the localization intersects the full ambient
ring in exactly `ℂ[Fₙ]` in every dimension `n ≥ 4`.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

@[simp] theorem extendedCoefficientMap_complex (n : ℕ) (a : ℂ) :
    extendedCoefficientMap n (algebraMap ℂ LaurentCoefficients a) =
      algebraMap ℂ (ExtendedLocalizedAmbient n) a := by
  change C (coefficientMap (algebraMap ℂ LaurentCoefficients a)) = _
  rw [coefficientMap_complex_intersection]
  rfl

end AbhyankarSathaye.CommutingDerivations

end

end OAI


