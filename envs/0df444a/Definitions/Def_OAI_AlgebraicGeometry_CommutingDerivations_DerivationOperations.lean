-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_DerivationOperations
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_DerivationOperations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:41:07.90866+00:00
-- url     : https://prove2.me/theorems/034977de-ed47-4d71-86ac-bc06d9d6a462
-- title:
--   Transport and descent of derivations along algebra maps
-- statement:
--   Let $K$ be a commutative ring and let $A$, $B$ be commutative $K$-algebras. Write $\operatorname{Der}_K(A)$ for the set of $K$-linear derivations $d:A\to A$, i.e. $K$-linear maps with $d(ab)=a\,d(b)+b\,d(a)$. The file defines two operations.
--
--   1. **Transport along an isomorphism.** For a $K$-algebra isomorphism $e:A\to B$ and $D\in\operatorname{Der}_K(B)$, the pulled-back derivation $e^{*}D\in\operatorname{Der}_K(A)$ given by
--
--      $$(e^{*}D)(a)=e^{-1}\bigl(D(e(a))\bigr)\qquad(a\in A).$$
--
--   2. **Descent along an injective map.** For an injective $K$-algebra homomorphism $\iota:A\to B$, a derivation $D\in\operatorname{Der}_K(B)$ and a function $d:A\to A$ satisfying
--
--      $$\iota\bigl(d(a)\bigr)=D\bigl(\iota(a)\bigr)\qquad\text{for all }a\in A,$$
--
--      the function $d$ itself, regarded as an element of $\operatorname{Der}_K(A)$. No additivity, linearity or Leibniz rule is assumed for $d$: each of these identities holds after applying $\iota$, because $D$ is a derivation and $\iota$ a homomorphism, and $\iota$ is injective.
--
--   Two simp lemmas state that these derivations act by the displayed formulas.
--
--   These are the two ways in which derivations move between the rings of the construction: partial derivatives in a polynomial presentation of a localized ring are pulled back to that ring by transport, and a derivation of a localization that maps the image of the original ring into itself descends to a derivation of the original ring. Local nilpotence and pairwise commutation are preserved by both operations (accompanying results).
--
--   **Formalization Note** Lean names: `transportDerivation e D` and `descendDerivation ι hι D d hd`, with the simp lemmas `transportDerivation_apply` and `descendDerivation_apply`. In `descendDerivation` the derivation laws for `d` are obtained from the injectivity hypothesis `hι`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/DerivationOperations.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/DerivationOperations.lean by skeleton subtraction
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

namespace OAI

/-!
Transport, scaling, and descent of derivations through algebra homomorphisms.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

/-- Pull a derivation back through an actual algebra equivalence. -/
def transportDerivation (e : A ≃ₐ[K] B) (D : Derivation K B B) : Derivation K A A where
  toLinearMap := e.symm.toLinearMap.comp (D.toLinearMap.comp e.toLinearMap)
  map_one_eq_zero' := by
    change e.symm (D (e 1)) = 0
    simp
  leibniz' a b := by
    change e.symm (D (e (a * b))) = a * e.symm (D (e b)) + b * e.symm (D (e a))
    simp [Derivation.leibniz, smul_eq_mul]

@[simp] theorem transportDerivation_apply (e : A ≃ₐ[K] B)
    (D : Derivation K B B) (a : A) :
    transportDerivation e D a = e.symm (D (e a)) := rfl

/-- A specified function whose image intertwines a derivation through an
injective algebra map automatically satisfies all derivation laws. -/
def descendDerivation (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (d : A → A) (hd : ∀ a, ι (d a) = D (ι a)) :
    Derivation K A A where
  toFun := d
  map_add' a b := by
    apply hι
    simp only [hd, map_add]
  map_smul' k a := by
    change d (k • a) = k • d a
    apply hι
    simp only [hd, map_smul, Derivation.map_smul]
  map_one_eq_zero' := by
    change d 1 = 0
    apply hι
    simp only [hd, map_one, Derivation.map_one_eq_zero, map_zero]
  leibniz' a b := by
    change d (a * b) = a * d b + b * d a
    apply hι
    simp only [hd, smul_eq_mul, map_mul, map_add, Derivation.leibniz]

@[simp] theorem descendDerivation_apply (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (d : A → A) (hd : ∀ a, ι (d a) = D (ι a)) (a : A) :
    descendDerivation ι hι D d hd a = d a := rfl

end AbhyankarSathaye.CommutingDerivations

end

end OAI


