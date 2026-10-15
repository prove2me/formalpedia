-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBezout
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_ParameterBezout
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:24:43.602431+00:00
-- url     : https://prove2.me/theorems/76beac18-232b-4175-bb36-bc80fc18271f
-- title:
--   Relative Bézout identity for $h$ and $y$ on the fibres $h=c+P(x,y,s)$
-- statement:
--   Let $K$ be a commutative ring and let $P(x,y,s)=-2s^2x+3sy^2-3s^3y$. For $c,x,y,s\in K$ define
--
--   $$A_c(x,s)=c+2s^2x+4s^5,\qquad B_c(x,y,s)=(3s^3-3sy)(c+2s^2x)-4s^4y^2 .$$
--
--   For $c=1$ these are the coefficients $\alpha(x,s)$ and $\beta(x,y,s)$. The file proves the following for all $h,c,d,s,x,y\in K$.
--
--   1. **Certificate.** The polynomial identity
--
--      $$A_c\,h+B_c\,y-c^2=(c+2s^2x)\bigl(h-c-P(x,y,s)\bigr)-4s^4\bigl(x^2+y^3-sh\bigr).$$
--
--   2. **Unit Bézout relation.** If $x^2+y^3=sh$, $h=c+P(x,y,s)$ and $cd=1$, then $(d^2A_c)\,h+(d^2B_c)\,y=1$.
--   3. **Shift.** If $x^2+y^3=sh$ and $h=c+P(x,y,s)$, then $(x+s^3)^2+(y-s^2)^3=cs$.
--   4. **Recovering $s$.** If in addition $cd=1$, then $d\bigl((x+s^3)^2+(y-s^2)^3\bigr)=s$.
--   5. **Naturality.** Every ring homomorphism $f$ satisfies $f(A_c(x,s))=A_{f(c)}(f(x),f(s))$ and $f(B_c(x,y,s))=B_{f(c)}(f(x),f(y),f(s))$.
--
--   In $\mathbb{C}[h,u,v,w]$ one has $h=c+P(x,y,s)$ for $c=F+1$, together with the cusp relation $x^2+y^3=hs$. Once $F+1$ is inverted, $h$ and $y$ therefore generate the unit ideal, with explicit coefficients $c^{-2}A_c$ and $c^{-2}B_c$. Moreover, $s=c^{-1}\bigl((x+s^3)^2+(y-s^2)^3\bigr)$ is a polynomial in the shifted coordinates. These are the inputs of the linear lifting formulas that produce explicit polynomial coordinates on the localization. Everything is stated over an arbitrary commutative ring, so the lemmas apply equally in quotients, in localizations and in polynomial rings over Laurent coefficients.
--
--   **Formalization Note** $A_c$ and $B_c$ are `parameterA c x s` and `parameterB c x y s`. The inverse of $c$ is passed as an element $d$ with the hypothesis `c * d = 1`. The naturality statements `map_parameterA` and `map_parameterB` are simp lemmas for any `RingHomClass`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/ParameterBezout.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ParameterBezout.lean by skeleton subtraction
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

namespace OAI

/-!
A relative Bézout identity over an arbitrary commutative ring.
The inverse of `c` is specified by the equation `c * d = 1`.
-/
namespace AbhyankarSathaye.CommutingDerivations

variable {K : Type*} [CommRing K]

def parameterA (c x s : K) : K := c + 2*s^2*x + 4*s^5

def parameterB (c x y s : K) : K :=
  (3*s^3 - 3*s*y)*(c + 2*s^2*x) - 4*s^4*y^2

theorem parameter_bezout_certificate (h c s x y : K) :
    parameterA c x s*h + parameterB c x y s*y - c^2 =
      (c + 2*s^2*x)*(h - c - P x y s) -
        4*s^4*(x^2 + y^3 - s*h) := by
  unfold parameterA parameterB P
  ring

theorem parameter_bezout_unit (h c d s x y : K)
    (hcusp : x^2 + y^3 = s*h) (hsection : h = c + P x y s)
    (hunit : c*d = 1) :
    (d^2*parameterA c x s)*h + (d^2*parameterB c x y s)*y = 1 := by
  have hz : h - c - P x y s = 0 := by rw [hsection]; ring
  have hb : parameterA c x s*h + parameterB c x y s*y = c^2 := by
    apply sub_eq_zero.mp
    rw [parameter_bezout_certificate, hz, hcusp, sub_self]
    ring
  calc
    _ = d^2*(parameterA c x s*h + parameterB c x y s*y) := by ring
    _ = d^2*c^2 := by rw [hb]
    _ = (c*d)^2 := by ring
    _ = 1 := by rw [hunit]; ring

theorem parameter_shift (h c s x y : K)
    (hcusp : x^2 + y^3 = s*h) (hsection : h = c + P x y s) :
    (x + s^3)^2 + (y - s^2)^3 = c*s := by
  rw [shift_universal, hcusp, hsection]
  ring

theorem parameter_recover_s (h c d s x y : K)
    (hcusp : x^2 + y^3 = s*h) (hsection : h = c + P x y s)
    (hunit : c*d = 1) :
    d*((x + s^3)^2 + (y - s^2)^3) = s := by
  rw [parameter_shift h c s x y hcusp hsection]
  calc
    d*(c*s) = (c*d)*s := by ring
    _ = s := by rw [hunit, one_mul]

section Maps
variable {L H : Type*} [CommRing L] [FunLike H K L] [RingHomClass H K L]

@[simp] theorem map_parameterA (f : H) (c x s : K) :
    f (parameterA c x s) = parameterA (f c) (f x) (f s) := by
  simp [parameterA, map_ofNat]

@[simp] theorem map_parameterB (f : H) (c x y s : K) :
    f (parameterB c x y s) = parameterB (f c) (f x) (f y) (f s) := by
  simp [parameterB, map_ofNat]

end Maps
end AbhyankarSathaye.CommutingDerivations

end OAI


