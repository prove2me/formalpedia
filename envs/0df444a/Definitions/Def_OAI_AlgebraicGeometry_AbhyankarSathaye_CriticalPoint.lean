-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:31:17.759878+00:00
-- url     : https://prove2.me/theorems/862d22b9-60d2-4f3e-a4ad-678ff6da71bc
-- title:
--   The point $(h,u,v,w)=(2,0,-1/2,1/2)$ in $\mathbb{C}^4$
-- statement:
--   This file defines a single explicit point of complex affine $4$-space,
--   $$c=(c_h,c_u,c_v,c_w)=\Bigl(2,\ 0,\ -\tfrac12,\ \tfrac12\Bigr)\in\mathbb{C}^4,$$
--   with coordinates listed in the order $h,u,v,w$ of the variables of $R=\mathbb{C}[h,u,v,w]$, together with the four evaluation rules $c_h=2$, $c_u=0$, $c_v=-1/2$ and $c_w=1/2$.
--
--   The point is the witness that the explicit polynomial $F=h-P(x,y,s)-1\in R$ (with $x=u^3+hv$, $y=-u^2+hw$, $s=S(h,u,v,w)$) is not a coordinate. At $c$ one has $x=-1$, $y=1$ and $s=1$, hence $x+s^3=0$, $y-s^2=0$ and $F(c)=-1$; differentiating the ambient identity $(x+s^3)^2+(y-s^2)^3=s(1+F)$ then shows that every partial derivative of $F$ vanishes at $c$, whereas a coordinate polynomial has no such critical point.
--
--   **Formalization Note** `criticalPoint : Fin 4 → ℂ` is defined by nested `if`s on the index; `criticalPoint_h`, `criticalPoint_u`, `criticalPoint_v` and `criticalPoint_w` are its simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/CriticalPoint.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/CriticalPoint.lean by skeleton subtraction
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
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_FiberFormulas
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LinearPresentation

namespace OAI

/-!
# An explicit critical point away from the zero fiber

At `(h,u,v,w) = (2,0,-1/2,1/2)`, the value of `F` is `-1` and every
partial derivative vanishes. Differentiating the ambient polynomial identity
proves the latter without expanding `F`.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial

def criticalPoint (i : Fin 4) : ℂ :=
  if i = 0 then 2 else if i = 1 then 0 else if i = 2 then -1/2 else 1/2

@[simp] theorem criticalPoint_h : criticalPoint 0 = 2 := rfl
@[simp] theorem criticalPoint_u : criticalPoint 1 = 0 := rfl
@[simp] theorem criticalPoint_v : criticalPoint 2 = -1/2 := rfl
@[simp] theorem criticalPoint_w : criticalPoint 3 = 1/2 := rfl

end AbhyankarSathaye

end

end OAI


