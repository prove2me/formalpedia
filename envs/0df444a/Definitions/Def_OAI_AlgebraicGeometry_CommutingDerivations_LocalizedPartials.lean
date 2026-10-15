-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizedPartials
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_LocalizedPartials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:41:53.412729+00:00
-- url     : https://prove2.me/theorems/20ddef3d-5187-4577-b333-1348e904f138
-- title:
--   Coordinate partial derivatives transported through a polynomial presentation
-- statement:
--   Let $K$ be a commutative ring, let $B$ and $L$ be commutative $K$-algebras, let $I$ be an index set, and let $e:L\to B[Y_i: i\in I]$ be an isomorphism of $K$-algebras onto the polynomial ring over $B$ in the variables $Y_i$. For $i\in I$ the file defines the derivation $\partial^{e}_i$ of $L$ obtained by transporting the $i$-th coordinate partial derivative through $e$:
--
--   $$
--   \partial^{e}_i(a)=e^{-1}\Bigl(\frac{\partial\,e(a)}{\partial Y_i}\Bigr)\qquad(a\in L).
--   $$
--
--   Here $\partial/\partial Y_i$ is $B$-linear and is regarded as a $K$-linear derivation of $B[Y_i: i\in I]$, so $\partial^{e}_i$ is a $K$-linear derivation of $L$; a simp lemma states the displayed formula.
--
--   This turns a polynomial presentation of $L$ over a coefficient algebra $B$ into a family of derivations of $L$ with the familiar properties of partial derivatives, established in accompanying results: they commute pairwise, are locally nilpotent, satisfy $\partial^{e}_i\bigl(e^{-1}(Y_j)\bigr)=\delta_{ij}$, and annihilate every element that $e$ sends to a constant of $B$, even though they are only viewed as $K$-linear. In the main construction ($K=\mathbb{C}$), $L$ is the localization of $\mathbb{C}[X_0,\dots,X_{n-1}]$ away from $F_n+1$, $B$ is the Laurent ring $\mathbb{C}[c,c^{-1}]$ with $c$ corresponding to $F_n+1$, and $I$ has $n-1$ elements, which yields $n-1$ commuting locally nilpotent derivations of the localization that annihilate $F_n+1$.
--
--   **Formalization Note** The Lean definition is `localizedPartial e i`, built as `transportDerivation e` applied to `(pderiv i).restrictScalars K`; the simp lemma is `localizedPartial_apply`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/LocalizedPartials.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/LocalizedPartials.lean by skeleton subtraction
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
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_DerivationOperations

namespace OAI

/-! Transport the actual coordinate partials through a specified, proved
algebra equivalence. Coefficients in the whole relative coefficient algebra
are fixed, even when the derivations are viewed over a smaller ground ring. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K B L I : Type*} [CommRing K] [CommRing B] [CommRing L]
  [Algebra K B] [Algebra K L]

def localizedPartial (e : L ≃ₐ[K] MvPolynomial I B) (i : I) : Derivation K L L :=
  transportDerivation e ((pderiv i : Derivation B (MvPolynomial I B) _).restrictScalars K)

@[simp] theorem localizedPartial_apply (e : L ≃ₐ[K] MvPolynomial I B) (i : I) (a : L) :
    localizedPartial e i a = e.symm (pderiv i (e a)) := rfl

end AbhyankarSathaye.CommutingDerivations

end

end OAI


