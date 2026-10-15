-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:28:13.608984+00:00
-- url     : https://prove2.me/theorems/6f08bf5b-428d-4dcd-9bc6-b2eed7a54f06
-- title:
--   The zero fiber of $F$ has coordinate ring $\mathbb{C}[X_0,X_1,X_2]$
-- statement:
--   Notation: $R=\mathbb{C}[h,u,v,w]$ and $F=h-P(x,y,s)-1\in R$ with $x=u^3+hv$, $y=-u^2+hw$, $s=S(h,u,v,w)$. As before, $\mathcal P=\mathbb{C}[h,x,y,s]/(h-1-P(x,y,s),\ x^2+y^3-sh)$ is the plane presentation with generators $\bar h,\bar x,\bar y,\bar s$, and $L$ is the quotient of $\mathcal P[U,V,W]$ by $U^3+\bar hV-\bar x$, $-U^2+\bar hW-\bar y$ and $S(\bar h,U,V,W)-\bar s$. Let $\alpha(x,s)=1+2s^2x+4s^5$ and $\beta(x,y,s)=(3s^3-3sy)(1+2s^2x)-4s^4y^2$.
--
--   1. **Flattening.** The $\mathbb{C}$-algebra isomorphism $\mathbb{C}[X,Y][T]\cong\mathbb{C}[X_0,X_1,X_2]$ from polynomials in $T$ with coefficients in $\mathbb{C}[X,Y]$ to polynomials in three variables, with $X\mapsto X_0$, $Y\mapsto X_1$ and $T\mapsto X_2$ (a permutation of the variables is built in so that the new variable comes last).
--   2. **Lifted isomorphism.** The lifting isomorphism $L\cong\mathcal P[T]$, applied with $\alpha=\alpha(\bar x,\bar s)$ and $\beta=\beta(\bar x,\bar y,\bar s)$; its hypotheses $\bar x^2+\bar y^3=\bar h\bar s$ and $\alpha\bar h+\beta\bar y=1$ hold in $\mathcal P$. It is regarded as an isomorphism of $\mathbb{C}$-algebras.
--   3. **Plane extension.** The isomorphism $\mathcal P[T]\cong\mathbb{C}[X,Y][T]$ obtained by applying the plane isomorphism $\mathcal P\cong\mathbb{C}[X,Y]$ to the coefficients.
--   4. **Fiber isomorphism.** The composite $\mathbb{C}$-algebra isomorphism
--   $$R/(F)\ \cong\ L\ \cong\ \mathcal P[T]\ \cong\ \mathbb{C}[X,Y][T]\ \cong\ \mathbb{C}[X_0,X_1,X_2]$$
--   of the inverse of the elimination isomorphism followed by items 2, 3 and 1.
--
--   Item 4 is the first half of the main result in four variables: the hypersurface $F=0$ in $\mathbb{C}^4$ has the coordinate ring of affine $3$-space.
--
--   **Formalization Note** The items are `flattenPlane` (built from `MvPolynomial.finSuccEquiv ℂ 2` and the permutation `variableOrder` of `Fin 3`, with simp lemmas describing it on the variables), `liftedEquiv` (via `AlgEquiv.restrictScalars`), `planeExtensionEquiv` (via `Polynomial.mapAlgEquiv`) and `fiberEquiv : (R ⧸ Ideal.span {F}) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Fiber.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Fiber.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AbhyankarSathaye mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation

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

def liftedEquiv : L ≃ₐ[ℂ] Polynomial B :=
  (Lifting.equivalence hB xB yB sB (Alpha xB sB) (Beta xB yB sB)
    (Plane.relation_cusp ℂ) (Plane.bezout ℂ)).restrictScalars ℂ

def planeExtensionEquiv : Polynomial B ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin 2) ℂ) :=
  Polynomial.mapAlgEquiv (Plane.equivalence ℂ)

def fiberEquiv : (R ⧸ Ideal.span {F}) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  Presentation.eliminationEquiv.symm.trans
    (liftedEquiv.trans (planeExtensionEquiv.trans flattenPlane))

end AbhyankarSathaye

end

end OAI


