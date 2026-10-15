-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterRetraction
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_ParameterRetraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:36:22.897172+00:00
-- url     : https://prove2.me/theorems/f5a96951-0e96-46d0-9cbd-05ec97ef8e82
-- title:
--   The parameter $F+1$ and its retraction onto the line $(t,0,0,0)$
-- statement:
--   Let $R=\mathbb{C}[h,u,v,w]$ and let $F\in R$ be the polynomial of the construction, $F=h-P(x,y,s)-1$ with $x=u^3+hv$, $y=-u^2+hw$ and $s=S(h,u,v,w)$. The file defines the following objects.
--
--   1. **The parameter.** The element $F+1\in R$, which is the element inverted in the localization $R_{F+1}$.
--
--   2. **The slice retraction.** The $\mathbb{C}$-algebra homomorphism $\pi:R\to\mathbb{C}[t]$ with $\pi(h)=t$ and $\pi(u)=\pi(v)=\pi(w)=0$, i.e. restriction of polynomials to the line $(h,u,v,w)=(t,0,0,0)$.
--
--   On this line $x=y=s=0$, so $\pi(F+1)=t$, and consequently
--
--   $$
--   \pi\bigl(q(F+1)\bigr)=q(t)\qquad\text{for every }q\in\mathbb{C}[t];
--   $$
--
--   that is, $\pi$ is a left inverse of the substitution homomorphism $\mathbb{C}[t]\to R$, $q\mapsto q(F+1)$. Both identities are recorded as lemmas.
--
--   The retraction exhibits $\mathbb{C}[F+1]$ as a retract of $R$. It follows that the substitution $q\mapsto q(F+1)$ is injective, that $F+1\ne0$, and that whenever $(F+1)^m a=q(F+1)$ for some $a\in R$, $m\ge0$ and $q\in\mathbb{C}[t]$, the element $a$ is already the polynomial $\pi(a)$ evaluated at $F+1$. This saturation property identifies the elements of $R$ whose image in $R_{F+1}$ is a Laurent polynomial in $F+1$ with the polynomials in $F$, i.e. with $\mathbb{C}[F]$, the expected common kernel of the derivations.
--
--   **Formalization Note** Lean names: `ambientParameter` (defined as `F + 1`), `parameterSlice` ($\pi$, defined by `MvPolynomial.aeval` at the point with coordinates $t,0,0,0$), and the lemmas `parameterSlice_parameter`, `parameterSlice_aeval` (the composite with `Polynomial.aeval ambientParameter` is the identity) and `parameterSlice_aeval_apply`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/ParameterRetraction.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ParameterRetraction.lean by skeleton subtraction
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

namespace OAI

/-!
An explicit retraction proves saturation of the subring generated by `F + 1`.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

/-- The parameter inverted in the localization, `F + 1`. -/
def ambientParameter : R := F + 1

/-- Restriction to the line `(h,u,v,w)=(t,0,0,0)`. -/
def parameterSlice : R →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i : Fin 4 => if i = 0 then Polynomial.X else 0)

@[simp] theorem parameterSlice_parameter : parameterSlice ambientParameter = Polynomial.X := by
  simp [parameterSlice, ambientParameter, F, p, P, x, y, s, S, h, u, v, w]

theorem parameterSlice_aeval :
    parameterSlice.comp (Polynomial.aeval ambientParameter) = AlgHom.id ℂ (Polynomial ℂ) := by
  apply Polynomial.algHom_ext
  simp

@[simp] theorem parameterSlice_aeval_apply (q : Polynomial ℂ) :
    parameterSlice (Polynomial.aeval ambientParameter q) = q := by
  exact AlgHom.congr_fun parameterSlice_aeval q

end AbhyankarSathaye.CommutingDerivations

end

end OAI


