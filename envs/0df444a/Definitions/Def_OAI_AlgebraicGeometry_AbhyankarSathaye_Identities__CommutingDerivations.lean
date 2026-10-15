-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Identities__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:24:22.603744+00:00
-- url     : https://prove2.me/theorems/efcb6156-ea90-45eb-b0a0-f0fb3b2b28d4
-- title:
--   Cusp and shift identities for the explicit polynomial $F$ in $\mathbb{C}[h,u,v,w]$
-- statement:
--   Let $R=\mathbb{C}[h,u,v,w]$. For elements of any commutative ring set
--   $$S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3,\qquad P(x,y,s)=-2s^2x+3sy^2-3s^3y .$$
--   As in the base definitions, $x=u^3+hv$, $y=-u^2+hw$, $s=S(h,u,v,w)$, $p=P(x,y,s)$ and $F=h-p-1$ in $R$. This file adds the following objects and identities.
--
--   1. **Bézout-type coefficients.** For elements $x,y,s$ of a commutative ring $B$,
--
--      $$\alpha(x,s)=1+2s^2x+4s^5,\qquad \beta(x,y,s)=(3s^3-3sy)(1+2s^2x)-4s^4y^2 .$$
--
--   2. **Universal cusp identity.** For all $h,u,v,w$ in a commutative ring $B$,
--
--      $$(u^3+hv)^2+(-u^2+hw)^3=h\,S(h,u,v,w).$$
--
--   3. **Universal shift identity.** For all $x,y,s$ in a commutative ring $B$,
--
--      $$(x+s^3)^2+(y-s^2)^3=x^2+y^3-s\,P(x,y,s).$$
--
--   4. **Shifted coordinates.** The elements $\tilde X=x+s^3$ and $\tilde Y=y-s^2$ of $R$.
--
--   5. **Cusp relation in $R$.** $x^2+y^3=hs$. This is item 2 applied to the variables.
--
--   The map $(h,u,v,w)\mapsto(x,y,s)$ lands on the cuspidal family $x^2+y^3=hs$. Items 3 and 5 together give the relation $\tilde X^2+\tilde Y^3=s\,(1+F)$, on which the later constructions rest. After $F+1$ is inverted, this relation expresses $s$ through $\tilde X$ and $\tilde Y$, and these become free coordinates over the Laurent ring in $F+1$. At a point where $\tilde X=\tilde Y=0$, $s=1$ and $F=-1$, the same relation forces every partial derivative of $F$ to vanish. The coefficients $\alpha,\beta$ are the case $c=1$ of the relative Bézout coefficients for $h$ and $y$.
--
--   **Formalization Note** `Alpha`, `Beta`, `cusp_universal` and `shift_universal` are stated over an arbitrary commutative ring. `shiftX`, `shiftY` and `cusp` live in `R = MvPolynomial (Fin 4) ℂ`, whose variables `X 0, …, X 3` are $h,u,v,w$. The polynomials $S$, $P$, $x$, $y$, $s$, $p$ and $F$ come from the base definition file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Identities.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Identities.lean by skeleton subtraction
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

def shiftX : R := x + s^3
def shiftY : R := y - s^2

theorem cusp : x^2 + y^3 = h*s := cusp_universal h u v w

end AbhyankarSathaye

end

end OAI


