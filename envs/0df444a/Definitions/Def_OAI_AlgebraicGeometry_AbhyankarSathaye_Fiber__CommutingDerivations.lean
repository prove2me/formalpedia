-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:32:28.100986+00:00
-- url     : https://prove2.me/theorems/086ea384-3f42-4310-8571-64bfee0d2b9b
-- title:
--   Flattening isomorphism $\mathbb{C}[a,b][T]\cong\mathbb{C}[X_0,X_1,X_2]$
-- statement:
--   Let $\mathbb{C}[a,b]$ be the complex polynomial ring in two variables and $\mathbb{C}[a,b][T]$ the ring of polynomials in one further variable $T$ with coefficients in it. The file defines the following objects.
--
--   1. **Variable order.** The permutation $\sigma$ of $\{0,1,2\}$ with $\sigma(0)=2$, $\sigma(1)=0$, $\sigma(2)=1$.
--
--   2. **Flattening isomorphism.** The $\mathbb{C}$-algebra isomorphism
--
--      $$\Theta:\mathbb{C}[a,b][T]\xrightarrow{\ \sim\ }\mathbb{C}[X_0,X_1,X_2],\qquad \Theta(a)=X_0,\quad \Theta(b)=X_1,\quad \Theta(T)=X_2,$$
--
--      obtained by inverting the standard isomorphism $\mathbb{C}[Z_0,Z_1,Z_2]\cong\mathbb{C}[Z_1,Z_2][Z_0]$ (polynomials in the first variable with coefficients in the other two, with $a,b$ corresponding to $Z_1,Z_2$) and then renaming $Z_i\mapsto X_{\sigma(i)}$. Simp lemmas record the values of $\Theta$ on $a,b,T$ and of $\Theta^{-1}$ on $X_0,X_1,X_2$.
--
--   This is the last link in the chain of explicit isomorphisms describing the zero fiber of $F$: $\mathbb{C}[h,u,v,w]/(F)$ is identified with the lifting presentation $L$ over the plane presentation $B$, then $L\cong B[T]$ by the one-variable lifting isomorphism, $B[T]\cong\mathbb{C}[a,b][T]$ by the plane coordinates $a=x+s^3$, $b=y-s^2$ applied to coefficients, and finally $\Theta$ lands in $\mathbb{C}[X_0,X_1,X_2]$. Hence the hypersurface $F=0$ in $\mathbb{C}^4$ is isomorphic to affine $3$-space, with the two plane coordinates first and the lifting parameter last.
--
--   **Formalization Note** `variableOrder` is $\sigma$ and `flattenPlane` is $\Theta$, built from Mathlib's `finSuccEquiv` and `renameEquiv`. The simp lemmas are `flattenPlane_symm_X0`, `flattenPlane_symm_X1`, `flattenPlane_symm_X2`, `flattenPlane_C_X0`, `flattenPlane_C_X1` and `flattenPlane_X`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Fiber.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Fiber.lean by skeleton subtraction
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

namespace OAI

/-!
# The polynomial algebra structure of the zero fiber

Composing elimination, lifting, the plane parametrization, and a permutation
of variables gives the complex algebra isomorphism with `ℂ[X,Y,T]`.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial Presentation

def variableOrder : Fin 3 ≃ Fin 3 where
  toFun := ![2,0,1]
  invFun := ![1,2,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def flattenPlane : Polynomial (MvPolynomial (Fin 2) ℂ) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  (MvPolynomial.finSuccEquiv ℂ 2).symm.trans (renameEquiv ℂ variableOrder)

@[simp] theorem flattenPlane_symm_X0 : flattenPlane.symm (X 0) = Polynomial.C (X 0) := by
  change MvPolynomial.finSuccEquiv ℂ 2 (rename variableOrder.symm (X 0)) = _
  rw [rename_X]
  exact finSuccEquiv_X_succ (j := (0 : Fin 2))

@[simp] theorem flattenPlane_symm_X1 : flattenPlane.symm (X 1) = Polynomial.C (X 1) := by
  change MvPolynomial.finSuccEquiv ℂ 2 (rename variableOrder.symm (X 1)) = _
  rw [rename_X]
  exact finSuccEquiv_X_succ (j := (1 : Fin 2))

@[simp] theorem flattenPlane_symm_X2 : flattenPlane.symm (X 2) = Polynomial.X := by
  change MvPolynomial.finSuccEquiv ℂ 2 (rename variableOrder.symm (X 2)) = _
  rw [rename_X]
  exact finSuccEquiv_X_zero

@[simp] theorem flattenPlane_C_X0 : flattenPlane (Polynomial.C (X 0)) = X 0 := by
  apply flattenPlane.symm.injective
  simp
@[simp] theorem flattenPlane_C_X1 : flattenPlane (Polynomial.C (X 1)) = X 1 := by
  apply flattenPlane.symm.injective
  simp
@[simp] theorem flattenPlane_X : flattenPlane Polynomial.X = X 2 := by
  apply flattenPlane.symm.injective
  simp

end AbhyankarSathaye

end

end OAI


