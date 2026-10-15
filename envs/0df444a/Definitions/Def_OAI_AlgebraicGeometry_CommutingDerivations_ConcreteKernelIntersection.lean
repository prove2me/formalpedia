-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ConcreteKernelIntersection
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_ConcreteKernelIntersection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:38:37.856136+00:00
-- url     : https://prove2.me/theorems/ec333a96-79e1-41a3-a10e-dbd0cc872d6e
-- title:
--   The Laurent coefficient map $c\mapsto F+1$ on polynomials and constants
-- statement:
--   Let $R=\mathbb{C}[h,u,v,w]$, let $F\in R$ be the polynomial of the construction, let $R_{F+1}$ be the localization of $R$ away from $F+1$ with localization map $r\mapsto r/1$, and let $\Lambda=\mathbb{C}[c,c^{-1}]$ be the Laurent polynomial ring, realized as the localization of $\mathbb{C}[t]$ away from $t$ (so a polynomial $q\in\mathbb{C}[t]$ gives the element $q(c)\in\Lambda$). Companion files define the substitution homomorphism $\mathbb{C}[t]\to R_{F+1}$, $q\mapsto q\bigl((F+1)/1\bigr)$, and its extension $\kappa:\Lambda\to R_{F+1}$, which sends $c$ to $F+1$ and $c^{-1}$ to $(F+1)^{-1}$. The file records three evaluation lemmas.
--
--   1. For every $q\in\mathbb{C}[t]$, the substitution homomorphism sends $q$ to $q(F+1)/1$; that is, substituting the image of $F+1$ commutes with localization.
--
--   2. For every $q\in\mathbb{C}[t]$,
--
--      $$\kappa\bigl(q(c)\bigr)=\frac{q(F+1)}{1}\in R_{F+1}.$$
--
--   3. For every $a\in\mathbb{C}$, $\kappa(a)=a$: the complex constants of $\Lambda$ go to the complex constants of $R_{F+1}$.
--
--   These computations connect Laurent expressions in $c$ with ordinary polynomials in $F+1$. They are used to prove that an element $r\in R$ satisfies $r/1=\kappa(a)$ for some $a\in\Lambda$ if and only if $r$ is a polynomial in $F$, i.e. $r\in\mathbb{C}[F]$; this identifies the elements of $R$ lying in the coefficient ring of the localized coordinates with the expected common kernel.
--
--   **Formalization Note** The lemmas are `polynomialCoefficientMap_apply`, `coefficientMap_polynomial` and `coefficientMap_complex_intersection`; the substitution homomorphism is `polynomialCoefficientMap`, $\kappa$ is `coefficientMap` and $F+1$ is `ambientC`. The intersection theorem itself is not part of this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/ConcreteKernelIntersection.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ConcreteKernelIntersection.lean by skeleton subtraction
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

namespace OAI

/-!
The Laurent coefficient-map image intersects the ambient ring in exactly
`ℂ[F]`, by the explicit parameter retraction.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

theorem polynomialCoefficientMap_apply (q : Polynomial ℂ) :
    polynomialCoefficientMap q = loc (Polynomial.aeval ambientC q) := by
  have he := Polynomial.aeval_algHom
    (IsScalarTower.toAlgHom ℂ R LocalizedAmbient) ambientC
  exact AlgHom.congr_fun he q

@[simp] theorem coefficientMap_polynomial (q : Polynomial ℂ) :
    coefficientMap (algebraMap (Polynomial ℂ) LaurentCoefficients q) =
      loc (Polynomial.aeval ambientC q) := by
  rw [← polynomialCoefficientMap_apply]
  unfold coefficientMap
  exact IsLocalization.Away.lift_eq _ _ _

/-- Constants in the actual Laurent coefficient algebra have the prescribed
complex scalar image in the actual ambient localization. -/
@[simp] theorem coefficientMap_complex_intersection (a : ℂ) :
    coefficientMap (algebraMap ℂ LaurentCoefficients a) = algebraMap ℂ LocalizedAmbient a := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) LaurentCoefficients]
  rw [coefficientMap_polynomial]
  simp [loc, IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient]

end AbhyankarSathaye.CommutingDerivations

end

end OAI


