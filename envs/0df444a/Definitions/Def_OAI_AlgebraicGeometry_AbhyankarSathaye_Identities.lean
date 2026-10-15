-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Identities
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:23:11.767372+00:00
-- url     : https://prove2.me/theorems/e9311f6b-3595-4621-bd8a-f7c36d77f79d
-- title:
--   The cusp, shift and Bézout identities and the explicit polynomial $F\in\mathbb{C}[h,u,v,w]$
-- statement:
--   This file introduces the explicit polynomials of the construction and the polynomial identities they satisfy.
--
--   Let $B$ be any commutative ring. For elements $h,u,v,w,x,y,s\in B$ put
--   $$S(h,u,v,w)=2u^3v+3u^4w+h\,(v^2-3u^2w^2)+h^2w^3,\qquad P(x,y,s)=-2s^2x+3sy^2-3s^3y,$$
--   $$\alpha(x,s)=1+2s^2x+4s^5,\qquad \beta(x,y,s)=(3s^3-3sy)(1+2s^2x)-4s^4y^2 .$$
--
--   1. **Cusp identity.** For all $h,u,v,w\in B$,
--   $$(u^3+hv)^2+(-u^2+hw)^3=h\,S(h,u,v,w).$$
--   2. **Shift identity.** For all $x,y,s\in B$,
--   $$(x+s^3)^2+(y-s^2)^3=x^2+y^3-s\,P(x,y,s).$$
--   3. **Bézout certificate.** For all $h,x,y,s\in B$,
--   $$\alpha(x,s)\,h+\beta(x,y,s)\,y-1=(1+2s^2x)\bigl(h-1-P(x,y,s)\bigr)-4s^4\bigl(x^2+y^3-sh\bigr).$$
--   4. **The explicit polynomial.** In the polynomial ring $R=\mathbb{C}[h,u,v,w]$ in four variables define
--   $$x=u^3+hv,\qquad y=-u^2+hw,\qquad s=S(h,u,v,w),\qquad p=P(x,y,s),\qquad F=h-p-1,$$
--   together with the shifted elements $x+s^3$ and $y-s^2$. Specializing the identities above gives $x^2+y^3=hs$, $(x+s^3)^2+(y-s^2)^3=x^2+y^3-sp$, and the *ambient identity*
--   $$(x+s^3)^2+(y-s^2)^3=s\,(1+F).$$
--
--   The polynomial $F$ is the central object of the construction: the coordinate ring $R/(F)$ of the hypersurface $F=0$ in $\mathbb{C}^4$ turns out to be a polynomial ring in three variables, although $F$ is not a coordinate of $R$. The cusp identity places $(x,y)$ on the relation $x^2+y^3=hs$; the Bézout certificate shows that $h$ and $y$ generate the unit ideal as soon as $h=1+P(x,y,s)$ and $x^2+y^3=hs$; and the ambient identity is the relation that later forces all partial derivatives of $F$ to vanish at a point where $F=-1$.
--
--   **Formalization Note** `S`, `P`, `Alpha`, `Beta` are defined over an arbitrary `CommRing`, where the identities `cusp_universal`, `shift_universal` and `bezout_certificate` are proved. `R` is `MvPolynomial (Fin 4) ℂ` with `h, u, v, w` the variables `X 0, X 1, X 2, X 3`; `x, y, s, p, F` are as above, `shiftX` and `shiftY` are $x+s^3$ and $y-s^2$, and the specialized identities are `cusp`, `shift` and `ambient`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Identities.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Identities.lean by skeleton subtraction
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

namespace OAI

/-!
# Polynomial identities for the cusp and the explicit hypersurface

The polynomials `S` and `P` give the identity
`(x + s³)² + (y - s²)³ = s * (1 + F)`. The Bézout certificate is valid over
every commutative ring. In the ambient complex polynomial ring, the variables
are ordered as `h, u, v, w`.
-/

noncomputable section
namespace AbhyankarSathaye

def S {B : Type*} [CommRing B] (h u v w : B) : B :=
  2*u^3*v + 3*u^4*w + h*(v^2 - 3*u^2*w^2) + h^2*w^3

def P {B : Type*} [CommRing B] (x y s : B) : B :=
  -2*s^2*x + 3*s*y^2 - 3*s^3*y

def Alpha {B : Type*} [CommRing B] (x s : B) : B :=
  1 + 2*s^2*x + 4*s^5

def Beta {B : Type*} [CommRing B] (x y s : B) : B :=
  (3*s^3 - 3*s*y)*(1 + 2*s^2*x) - 4*s^4*y^2

theorem cusp_universal {B : Type*} [CommRing B] (h u v w : B) :
    (u^3 + h*v)^2 + (-u^2 + h*w)^3 = h*S h u v w := by
  unfold S
  ring

theorem shift_universal {B : Type*} [CommRing B] (x y s : B) :
    (x + s^3)^2 + (y - s^2)^3 = x^2 + y^3 - s*P x y s := by
  unfold P
  ring

theorem bezout_certificate {B : Type*} [CommRing B] (h x y s : B) :
    Alpha x s*h + Beta x y s*y - 1 =
      (1 + 2*s^2*x)*(h - 1 - P x y s) - 4*s^4*(x^2 + y^3 - s*h) := by
  unfold Alpha Beta P
  ring

abbrev R := MvPolynomial (Fin 4) ℂ

def h : R := MvPolynomial.X 0
def u : R := MvPolynomial.X 1
def v : R := MvPolynomial.X 2
def w : R := MvPolynomial.X 3
def x : R := u^3 + h*v
def y : R := -u^2 + h*w
def s : R := S h u v w
def p : R := P x y s
def F : R := h - p - 1
def shiftX : R := x + s^3
def shiftY : R := y - s^2

theorem cusp : x^2 + y^3 = h*s := cusp_universal h u v w

theorem shift : shiftX^2 + shiftY^3 = x^2 + y^3 - s*p :=
  shift_universal x y s

theorem ambient : shiftX^2 + shiftY^3 = s*(1 + F) := by
  rw [shift, cusp]
  unfold F
  ring

end AbhyankarSathaye

end

end OAI


