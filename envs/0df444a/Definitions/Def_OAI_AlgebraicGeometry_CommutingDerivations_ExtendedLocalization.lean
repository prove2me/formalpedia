-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedLocalization
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_ExtendedLocalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:36:03.467476+00:00
-- url     : https://prove2.me/theorems/88f44cef-294a-455f-bcc8-c2ada99f7e80
-- title:
--   Localization coordinates over Laurent polynomials in every dimension $n\ge4$
-- statement:
--   Let $R=\mathbb{C}[h,u,v,w]$, let $F\in R$ be the polynomial of the construction, let $R_{F+1}=R[(F+1)^{-1}]$ be the localization of $R$ away from $F+1$, and let $\Lambda=\mathbb{C}[c,c^{-1}]$ be the ring of complex Laurent polynomials, realized as the localization of $\mathbb{C}[t]$ away from $t$. Companion files provide the ring homomorphism $\kappa:\Lambda\to R_{F+1}$ with $\kappa(c)=F+1$ and a $\mathbb{C}$-algebra isomorphism $\Omega:R_{F+1}\xrightarrow{\sim}\Lambda[X,Y,T]$ with $\Omega(\kappa(a))=a$ for all $a\in\Lambda$. For $n\ge4$ let $\Sigma_n:\mathbb{C}[X_0,\dots,X_{n-1}]\xrightarrow{\sim}R[Z_0,\dots,Z_{n-5}]$ be the splitting isomorphism ($X_0,X_1,X_2,X_3\mapsto h,u,v,w$ and $X_{4+j}\mapsto Z_j$), and let $F_n$ be the copy of $F$ in the first four variables. The file defines the following objects.
--
--   1. **Extended localized ring.** $E_n=R_{F+1}[Z_0,\dots,Z_{n-5}]$, the polynomial ring in $n-4$ variables over $R_{F+1}$.
--
--   2. **Structure map.** The $\mathbb{C}$-algebra homomorphism $\lambda_n:\mathbb{C}[X_0,\dots,X_{n-1}]\to E_n$ obtained by composing $\Sigma_n$ with the coefficientwise localization map $R\to R_{F+1}$, its underlying ring homomorphism, and the resulting algebra structure of $E_n$ over $\mathbb{C}[X_0,\dots,X_{n-1}]$. One has $\lambda_n(F_n+1)=F+1$, a constant.
--
--   3. **Coefficient map.** $\kappa_n:\Lambda\to E_n$, sending $a$ to the constant polynomial $\kappa(a)$; thus $\kappa_n(c)=F+1$.
--
--   4. **Localization coordinates.** The $\mathbb{C}$-algebra isomorphism
--
--      $$\Omega_n:E_n\xrightarrow{\ \sim\ }\Lambda[Y_0,\dots,Y_{n-2}]$$
--
--      obtained by applying $\Omega$ to every coefficient, merging $\Lambda[X,Y,T][Z_0,\dots,Z_{n-5}]$ into a single polynomial ring, and renaming $X,Y,T\mapsto Y_0,Y_1,Y_2$ and $Z_j\mapsto Y_{3+j}$. It satisfies
--
--      $$\Omega_n\bigl(\kappa_n(a)\bigr)=a\quad(a\in\Lambda),\qquad \Omega_n\bigl(\lambda_n(F_n+1)\bigr)=c .$$
--
--   Thus, in every dimension $n\ge4$, the ring $E_n$, which an accompanying result shows to be the localization of $\mathbb{C}[X_0,\dots,X_{n-1}]$ away from $F_n+1$ via $\lambda_n$, has exactly $n-1$ polynomial coordinates over the Laurent ring $\Lambda$, and in these coordinates $F_n+1$ becomes the constant $c$. The coordinate partial derivatives are then commuting, locally nilpotent derivations that annihilate $\Lambda$, in particular $F_n+1$; they are the localized form of the derivations in the main construction.
--
--   **Formalization Note** `ExtendedLocalizedAmbient n` is `MvPolynomial (Fin (n-4)) LocalizedAmbient`, with natural-number subtraction; the other objects require $4\le n$. Lean names: `extendedLocAlgHom` ($\lambda_n$), `extendedLocMap` (its ring homomorphism), `extendedAlgebra` (the algebra structure, a definition rather than a global instance), `extendedCoefficientMap` ($\kappa_n$, defined for every $n$) and `extendedLocalizationEquiv` ($\Omega_n$); the lemmas `extendedLocMap_c`, `extendedLocalizationEquiv_coefficient` and `extendedLocalizationEquiv_c` are the displayed identities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedLocalization.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedLocalization.lean by skeleton subtraction
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

namespace OAI

/-!
Localization coordinates in every dimension `n ≥ 4`.

The localization at `extendedF hn + 1` is a polynomial extension of the
four-dimensional localization, with an explicit structural map from the ambient ring.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

abbrev ExtendedLocalizedAmbient (n : ℕ) := MvPolynomial (Fin (n-4)) LocalizedAmbient

def extendedLocAlgHom {n : ℕ} (hn : 4 ≤ n) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] ExtendedLocalizedAmbient n :=
  (MvPolynomial.mapAlgHom (σ := Fin (n-4))
    (IsScalarTower.toAlgHom ℂ R LocalizedAmbient)).comp (splitAmbient hn).toAlgHom

def extendedLocMap {n : ℕ} (hn : 4 ≤ n) :
    MvPolynomial (Fin n) ℂ →+* ExtendedLocalizedAmbient n :=
  (extendedLocAlgHom hn).toRingHom

@[instance_reducible]
def extendedAlgebra {n : ℕ} (hn : 4 ≤ n) :
    Algebra (MvPolynomial (Fin n) ℂ) (ExtendedLocalizedAmbient n) :=
  (extendedLocMap hn).toAlgebra

@[simp] theorem extendedLocMap_c {n : ℕ} (hn : 4 ≤ n) :
    extendedLocMap hn (extendedF hn+1) = C (loc ambientC) := by
  simp [extendedLocMap, extendedLocAlgHom, splitAmbient_F, ambientC, loc]
  change MvPolynomial.map (algebraMap R LocalizedAmbient) (C F) =
    C ((algebraMap R LocalizedAmbient) F)
  exact map_C _ _

def extendedCoefficientMap (n : ℕ) : LaurentCoefficients →+* ExtendedLocalizedAmbient n :=
  C.comp coefficientMap

/-- Complex-linear localization coordinates, with exactly n−1 independent
polynomial variables and the original Laurent coefficient ring. -/
def extendedLocalizationEquiv {n : ℕ} (hn : 4 ≤ n) :
    ExtendedLocalizedAmbient n ≃ₐ[ℂ] MvPolynomial (Fin (n-1)) LaurentCoefficients :=
  (MvPolynomial.mapAlgEquiv (Fin (n-4)) localizationComplexEquiv).trans
    (((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm.restrictScalars ℂ).trans
      ((renameEquiv LaurentCoefficients (blocksToOutput hn)).restrictScalars ℂ))

@[simp] theorem extendedLocalizationEquiv_coefficient {n : ℕ} (hn : 4 ≤ n)
    (a : LaurentCoefficients) :
    extendedLocalizationEquiv hn (extendedCoefficientMap n a) = C a := by
  have ha : localizationComplexEquiv (coefficientMap a) = C a :=
    relativeForward_coefficient a
  change rename (blocksToOutput hn)
    ((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm
      (MvPolynomial.map localizationComplexEquiv (C (coefficientMap a)))) = C a
  rw [map_C]
  change rename (blocksToOutput hn)
    ((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm
      (C (localizationComplexEquiv (coefficientMap a)))) = C a
  rw [ha, sumAlgEquiv_symm_C_C, rename_C]

@[simp] theorem extendedLocalizationEquiv_c {n : ℕ} (hn : 4 ≤ n) :
    extendedLocalizationEquiv hn (extendedLocMap hn (extendedF hn+1)) = C coefficientC := by
  rw [extendedLocMap_c, ← coefficientMap_C]
  exact extendedLocalizationEquiv_coefficient hn coefficientC

end AbhyankarSathaye.CommutingDerivations

end

end OAI


