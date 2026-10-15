-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:34:14.779492+00:00
-- url     : https://prove2.me/theorems/f0ac131a-d597-4a67-9897-39c2a980eb94
-- title:
--   The point $(2,0,-\tfrac12,\tfrac12)$, a critical point of $F$ on the fiber $F=-1$
-- statement:
--   Let $R=\mathbb{C}[h,u,v,w]$, with the variables in the order $h,u,v,w$, and let $F=h-P(x,y,s)-1\in R$, where $x=u^3+hv$, $y=-u^2+hw$, $s=S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$ and $P(x,y,s)=-2s^2x+3sy^2-3s^3y$. The file defines the point
--
--   $$
--   \mathbf{c}=(c_h,c_u,c_v,c_w)=\Bigl(2,\ 0,\ -\tfrac12,\ \tfrac12\Bigr)\in\mathbb{C}^4,
--   $$
--
--   given as a function from the four variable indices to $\mathbb{C}$, together with four simp lemmas returning its coordinates.
--
--   At $\mathbf{c}$ one has $x=-1$, $y=1$, $s=1$ and $P(x,y,s)=2$, hence $F(\mathbf{c})=-1$; moreover $x+s^3=0$ and $y-s^2=0$ there. The accompanying results show that every partial derivative of $F$ vanishes at $\mathbf{c}$, by differentiating the identity $(x+s^3)^2+(y-s^2)^3=s\,(1+F)$, so $\mathbf{c}$ is a singular point of the fiber $F=-1$. Because a coordinate of a polynomial ring has no point where all its partial derivatives vanish, this point witnesses that $F$ is not a coordinate of $\mathbb{C}[h,u,v,w]$, although its zero fiber is isomorphic to affine $3$-space.
--
--   **Formalization Note** The Lean definition `criticalPoint` is given by nested if-then-else on the index in `Fin 4`; the lemmas `criticalPoint_h`, `criticalPoint_u`, `criticalPoint_v` and `criticalPoint_w` evaluate it at the indices $0,1,2,3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/CriticalPoint.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/CriticalPoint.lean by skeleton subtraction
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


