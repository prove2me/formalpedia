-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationSetup
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_LocalizationSetup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:26:18.653233+00:00
-- url     : https://prove2.me/theorems/3c95ab64-e60a-4c37-8f4a-0618a822160b
-- title:
--   Localization of $\mathbb{C}[h,u,v,w]$ at $F+1$ and the coordinate candidates $x+s^3$, $y-s^2$, $T$
-- statement:
--   Let $R=\mathbb{C}[h,u,v,w]$ and take $x=u^3+hv$, $y=-u^2+hw$, $s=S(h,u,v,w)$ and $F=h-P(x,y,s)-1$ as in the base definitions. Write $\tilde X=x+s^3$ and $\tilde Y=y-s^2$, and let $A_c$, $B_c$ be the relative Bézout coefficients. The file sets up the following objects.
--
--   1. **The parameter and the localization.** The element $c=F+1\in R$, the localization $R_c=R[c^{-1}]$ with its canonical map $\lambda\colon R\to R_c$, and the inverse $c^{-1}\in R_c$. The file records $\lambda(c)\,c^{-1}=1$. Below, elements of $R$ are identified with their images under $\lambda$.
--   2. **Laurent coefficients.** The ring $\Lambda=\mathbb{C}[t,t^{-1}]$, realized as the localization of $\mathbb{C}[t]$ at $t$, with its elements $t$ and $t^{-1}$ satisfying $t\,t^{-1}=1$. The *relative plane* is the polynomial ring $\Lambda[X,Y,T]$ in three variables over $\Lambda$.
--   3. **Coefficient map.** $\kappa\colon\Lambda\to R_c$ is the unique ring homomorphism extending $\mathbb{C}[t]\to R_c$, $q\mapsto q(c)$. It satisfies $\kappa(t)=c$ and $\kappa(t^{-1})=c^{-1}$.
--   4. **Local Bézout coefficients and the third coordinate.** In $R_c$ the file defines
--      $$\alpha=c^{-2}A_c(x,s),\qquad \beta=c^{-2}B_c(x,y,s),\qquad \theta=\alpha u+\beta\,(v+uw),$$
--      together with the coordinate triple $(\tilde X,\tilde Y,\theta)$.
--   5. **Relations in $R_c$.** The file proves $x^2+y^3=sh$, $h=c+P(x,y,s)$, $\alpha h+\beta y=1$ and $c^{-1}\bigl(\tilde X^2+\tilde Y^3\bigr)=s$.
--   6. **Backward map.** $\Phi\colon\Lambda[X,Y,T]\to R_c$ is the ring homomorphism that equals $\kappa$ on coefficients and sends $X\mapsto\tilde X$, $Y\mapsto\tilde Y$ and $T\mapsto\theta$.
--
--   These objects are the ingredients of the explicit isomorphism $R[(F+1)^{-1}]\cong\Lambda[X,Y,T]$ with $F+1\mapsto t$, and $\Phi$ is its inverse direction. Through that isomorphism, the partial derivatives in $X$, $Y$ and $T$ become commuting, locally nilpotent derivations of $R_c$ that annihilate $F+1$. Clearing denominators in these derivations yields commuting derivations of the polynomial ring whose common kernel is $\mathbb{C}[F]$.
--
--   **Formalization Note** The Lean names are `ambientC` for $c$, `LocalizedAmbient` for $R_c$ (as `Localization.Away`), `LaurentCoefficients` for $\Lambda$, `RelativePlane` for $\Lambda[X,Y,T]$ (as `MvPolynomial (Fin 3)`), `loc` for $\lambda$ and `coefficientMap` for $\kappa$. Further, `coefficientC` and `coefficientD` are $t$ and $t^{-1}$, `localD` is $c^{-1}$, `localAlpha`, `localBeta` and `localT` are $\alpha$, $\beta$ and $\theta$, and `relativeBackward` is $\Phi$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/LocalizationSetup.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/LocalizationSetup.lean by skeleton subtraction
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

namespace OAI

/-!
The Laurent coefficient algebra and localization coordinates.
The coefficient map is the lift of `t ↦ F + 1`.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

def ambientC : R := F + 1
abbrev LocalizedAmbient := Localization.Away ambientC
abbrev LaurentCoefficients := Localization.Away (Polynomial.X : Polynomial ℂ)
abbrev RelativePlane := MvPolynomial (Fin 3) LaurentCoefficients

def loc : R →+* LocalizedAmbient := algebraMap R LocalizedAmbient
def coefficientC : LaurentCoefficients :=
  algebraMap (Polynomial ℂ) LaurentCoefficients Polynomial.X
def coefficientD : LaurentCoefficients :=
  IsLocalization.Away.invSelf (Polynomial.X : Polynomial ℂ)
def localD : LocalizedAmbient := IsLocalization.Away.invSelf ambientC

theorem coefficient_unit : coefficientC * coefficientD = 1 :=
  IsLocalization.Away.mul_invSelf _

theorem local_unit : loc ambientC * localD = 1 :=
  IsLocalization.Away.mul_invSelf _

def polynomialCoefficientMap : Polynomial ℂ →+* LocalizedAmbient :=
  (Polynomial.aeval (loc ambientC)).toRingHom

def coefficientMap : LaurentCoefficients →+* LocalizedAmbient :=
  IsLocalization.Away.lift Polynomial.X
    (by
      refine ⟨⟨polynomialCoefficientMap Polynomial.X, localD, ?_, ?_⟩, rfl⟩
      · simpa [polynomialCoefficientMap] using local_unit
      · simpa [polynomialCoefficientMap, mul_comm] using local_unit)

@[simp] theorem coefficientMap_C : coefficientMap coefficientC = loc ambientC := by
  simp [coefficientMap, coefficientC, polynomialCoefficientMap]

@[simp] theorem coefficientMap_D : coefficientMap coefficientD = localD := by
  have h1 : loc ambientC * coefficientMap coefficientD = 1 := by
    simpa using congrArg coefficientMap coefficient_unit
  calc
    coefficientMap coefficientD = (loc ambientC * localD) * coefficientMap coefficientD := by
      rw [local_unit, one_mul]
    _ = localD * (loc ambientC * coefficientMap coefficientD) := by ring
    _ = localD := by rw [h1, mul_one]

def localAlpha : LocalizedAmbient := localD^2 * parameterA (loc ambientC) (loc x) (loc s)
def localBeta : LocalizedAmbient :=
  localD^2 * parameterB (loc ambientC) (loc x) (loc y) (loc s)
def localT : LocalizedAmbient := parameter localAlpha localBeta (loc u) (loc v) (loc w)
def localCoordinates : Fin 3 → LocalizedAmbient := ![loc shiftX, loc shiftY, localT]

theorem local_cusp : (loc x)^2 + (loc y)^3 = loc s * loc h := by
  simpa [mul_comm] using congrArg loc cusp

theorem local_section : loc h = loc ambientC + P (loc x) (loc y) (loc s) := by
  have he : h = ambientC + P x y s := by unfold ambientC F p; ring
  simpa using congrArg loc he

theorem local_bezout : localAlpha * loc h + localBeta * loc y = 1 :=
  parameter_bezout_unit _ _ _ _ _ _ local_cusp local_section local_unit

theorem local_recover_s : localD * ((loc shiftX)^2 + (loc shiftY)^3) = loc s := by
  simpa [shiftX, shiftY] using
    parameter_recover_s _ _ _ _ _ _ local_cusp local_section local_unit

/-- Evaluation at the displayed X,Y,T, with the explicit relative coefficient map. -/
def relativeBackward : RelativePlane →+* LocalizedAmbient :=
  eval₂Hom coefficientMap localCoordinates

@[simp] theorem relativeBackward_C (a : LaurentCoefficients) :
    relativeBackward (C a) = coefficientMap a := by
  simp [relativeBackward]

@[simp] theorem relativeBackward_X (i : Fin 3) :
    relativeBackward (X i) = localCoordinates i := by
  simp [relativeBackward]

end AbhyankarSathaye.CommutingDerivations

end

end OAI


