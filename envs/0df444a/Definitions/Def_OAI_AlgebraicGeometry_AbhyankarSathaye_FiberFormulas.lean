-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_FiberFormulas
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_FiberFormulas
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:28:57.375178+00:00
-- url     : https://prove2.me/theorems/8c412b80-7171-4dd3-ab99-2fc42116439b
-- title:
--   Explicit formulas for the inverse of the zero-fiber isomorphism
-- statement:
--   Let $R=\mathbb{C}[h,u,v,w]$, with $x=u^3+hv$, $y=-u^2+hw$, $s=S(h,u,v,w)$ and $F=h-P(x,y,s)-1$, and let
--   $$\Phi:\ R/(F)\ \xrightarrow{\ \cong\ }\ \mathbb{C}[X_0,X_1,X_2]$$
--   be the fiber isomorphism of $\mathbb{C}$-algebras. For $g\in R$ write $[g]$ for its class in $R/(F)$, and let $\alpha(x,s)=1+2s^2x+4s^5$ and $\beta(x,y,s)=(3s^3-3sy)(1+2s^2x)-4s^4y^2$.
--
--   1. **The first two coordinates.** $\Phi^{-1}(X_0)=[x+s^3]$ and $\Phi^{-1}(X_1)=[y-s^2]$.
--   2. **Polynomials in the first two coordinates.** In $\mathbb{C}[X_0,X_1,X_2]$ define
--   $$\sigma=X_0^2+X_1^3,\quad \xi=X_0-\sigma^3,\quad \eta=X_1+\sigma^2,\quad \chi=1+P(\xi,\eta,\sigma),\quad a=\alpha(\xi,\sigma),\quad b=\beta(\xi,\eta,\sigma).$$
--   3. **Their preimages.**
--   $$\Phi^{-1}(\sigma)=[s],\quad \Phi^{-1}(\xi)=[x],\quad \Phi^{-1}(\eta)=[y],\quad \Phi^{-1}(\chi)=[h],\quad \Phi^{-1}(a)=[\alpha(x,s)],\quad \Phi^{-1}(b)=[\beta(x,y,s)].$$
--
--   These formulas make the isomorphism explicit on the elements built from $h,x,y,s$: on the hypersurface $F=0$, the functions $h$, $x$, $y$, $s$ and the Bézout coefficients are polynomials in the two coordinates $x+s^3$ and $y-s^2$ alone, while the third coordinate $X_2$ corresponds to the free variable $T$ of the lifting step.
--
--   **Formalization Note** $\Phi$ is `fiberEquiv` and $[g]$ is `dmap g`. Item 1 is `fiberEquiv_symm_X0` and `fiberEquiv_symm_X1` (stated with `shiftX` and `shiftY`); item 2 consists of `freeS`, `freeX`, `freeY`, `freeH`, `freeAlpha`, `freeBeta`; item 3 consists of the simp lemmas `symm_freeS`, `symm_freeX`, `symm_freeY`, `symm_freeH`, `symm_freeAlpha` and `symm_freeBeta`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/FiberFormulas.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/FiberFormulas.lean by skeleton subtraction
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
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber

namespace OAI

/-!
# Explicit coordinates on the zero fiber

The inverse isomorphism sends `X`, `Y`, and `T` to `x + s³`, `y - s²`,
and `α * u + β * (v + u * w)`. The forward isomorphism is given by the
polynomials `freeH`, `freeU`, `freeV`, and `freeW`, with variables ordered `X, Y, T`.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial Presentation

theorem fiberEquiv_symm_X0 : fiberEquiv.symm (X 0) = dmap shiftX := by
  change toOriginal (Lifting.backward hB xB yB sB (Alpha xB sB) (Beta xB yB sB)
    (Polynomial.map (Plane.backward ℂ).toRingHom (flattenPlane.symm (X 0)))) = _
  rw [flattenPlane_symm_X0, Polynomial.map_C]
  have he : (Plane.backward ℂ).toRingHom (X 0) = xB+sB^3 := by simp [Plane.backward]
  rw [he]
  simp only [Lifting.backward, Polynomial.aeval_C]
  change toOriginal (lcoef (xB+sB^3)) = _
  simp [auxValues, shiftX]

theorem fiberEquiv_symm_X1 : fiberEquiv.symm (X 1) = dmap shiftY := by
  change toOriginal (Lifting.backward hB xB yB sB (Alpha xB sB) (Beta xB yB sB)
    (Polynomial.map (Plane.backward ℂ).toRingHom (flattenPlane.symm (X 1)))) = _
  rw [flattenPlane_symm_X1, Polynomial.map_C]
  have he : (Plane.backward ℂ).toRingHom (X 1) = yB-sB^2 := by simp [Plane.backward]
  rw [he]
  simp only [Lifting.backward, Polynomial.aeval_C]
  change toOriginal (lcoef (yB-sB^2)) = _
  simp [auxValues, shiftY]

def freeS : MvPolynomial (Fin 3) ℂ := X 0^2+X 1^3
def freeX : MvPolynomial (Fin 3) ℂ := X 0-freeS^3
def freeY : MvPolynomial (Fin 3) ℂ := X 1+freeS^2
def freeH : MvPolynomial (Fin 3) ℂ := 1+P freeX freeY freeS
def freeAlpha : MvPolynomial (Fin 3) ℂ := Alpha freeX freeS
def freeBeta : MvPolynomial (Fin 3) ℂ := Beta freeX freeY freeS
@[simp] theorem symm_freeS : fiberEquiv.symm freeS = dmap s := by
  have ha := congrArg dmap ambient
  simp only [map_add, map_pow, map_mul, map_one, dmap_F, add_zero, mul_one] at ha
  simpa [freeS, fiberEquiv_symm_X0, fiberEquiv_symm_X1] using ha

@[simp] theorem symm_freeX : fiberEquiv.symm freeX = dmap x := by
  simp [freeX, fiberEquiv_symm_X0, shiftX]

@[simp] theorem symm_freeY : fiberEquiv.symm freeY = dmap y := by
  simp [freeY, fiberEquiv_symm_X1, shiftY]

@[simp] theorem symm_freeH : fiberEquiv.symm freeH = dmap h := by
  have hf : dmap h-dmap p-1 = 0 := by simpa [F] using dmap_F
  have hh : 1+dmap p = dmap h := by
    calc
      _ = dmap h-(dmap h-dmap p-1) := by ring
      _ = dmap h := by rw [hf, sub_zero]
  simpa [freeH, p] using hh

@[simp] theorem symm_freeAlpha : fiberEquiv.symm freeAlpha = dmap (Alpha x s) := by
  simp [freeAlpha]
@[simp] theorem symm_freeBeta : fiberEquiv.symm freeBeta = dmap (Beta x y s) := by
  simp [freeBeta]

end AbhyankarSathaye

end

end OAI


