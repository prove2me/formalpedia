-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:24:46.988805+00:00
-- url     : https://prove2.me/theorems/0f6449c5-3ad1-4dc7-866b-acf42d679cef
-- title:
--   Linear equations behind the lifting construction: substitution, compatibility and Bézout solving
-- statement:
--   This file collects polynomial identities that turn the lifting equations into linear equations. Throughout, $B$ is an arbitrary commutative ring, all letters denote elements of $B$, and $S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$.
--
--   1. **Substitution.** For all $h,U,G,W$,
--   $$S(h,U,G-UW,W)=hG^2-2U(hW-U^2)G+(hW-U^2)^2W.$$
--   2. **Compatibility.** Identically $y^2(y+U^2)-h(s-hG^2+2UyG)=(hG-yU)^2+y^3-hs$. Hence, if $x^2+y^3=hs$ and $hG-yU=x$, then
--   $$y^2\,(y+U^2)=h\,(s-hG^2+2UyG).$$
--   3. **Squared Bézout relation.** If $\alpha h+\beta y=1$, then $\alpha(1+\beta y)\,h+\beta^2y^2=1$.
--   4. **Solving two compatible linear equations.** Suppose $ca=hb$ and $rh+qc=1$. Then $W_0=ra+qb$ satisfies $hW_0=a$ and $cW_0=b$. Moreover, if only $rh+qc=1$ is assumed, any $W$ with $hW=a$ and $cW=b$ equals $ra+qb$.
--   5. **Parametrizing the relation $hG-yU=x$.** Assume $\alpha h+\beta y=1$. For every $T$, the pair $U=hT-\beta x$, $G=yT+\alpha x$ satisfies
--   $$hG-yU=x\qquad\text{and}\qquad \alpha U+\beta G=T.$$
--   Conversely, if $hG-yU=x$, then $U=h(\alpha U+\beta G)-\beta x$ and $G=y(\alpha U+\beta G)+\alpha x$.
--   6. **Change of unknowns.** If $U^3+hV=x$, $-U^2+hW=y$ and $S(h,U,V,W)=s$, then $G=V+UW$ satisfies
--   $$hG-yU=x,\qquad hW=y+U^2,\qquad y^2W=s-hG^2+2UyG .$$
--   Conversely, if $U,G,W$ satisfy these three equations, then $V=G-UW$ satisfies $U^3+hV=x$, $-U^2+hW=y$ and $S(h,U,V,W)=s$.
--
--   Together these identities show that, in the presence of a cusp relation $x^2+y^3=hs$ and a Bézout relation $\alpha h+\beta y=1$, the system $U^3+hV=x$, $-U^2+hW=y$, $S(h,U,V,W)=s$ is equivalent to a single linear relation in $(U,G)$, whose solutions are parametrized by $T=\alpha U+\beta G$, followed by two compatible linear equations for $W$ with coefficients $h$ and $y^2$, which generate the unit ideal. No cancellation is used, so everything holds in rings with zero divisors as well.
--
--   **Formalization Note** The lemmas are `substitute_S` (item 1), `compatibility_identity` and `compatibility` (item 2), `squared_bezout` (item 3), `solve_h`, `solve_c`, `solve_unique` (item 4), `linear_parameter_relation`, `linear_parameter_inverse`, `recover_U`, `recover_G` (item 5) and `original_to_linear`, `linear_to_original` (item 6), all stated for an arbitrary `CommRing`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/LiftingIdentities.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/LiftingIdentities.lean by skeleton subtraction
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

namespace OAI

/-!
# Linear equations for the lifting construction

The substitution `G = V + U * W` makes the equations linear in `W`.
A Bézout relation gives existence and uniqueness without cancellation.
-/

namespace AbhyankarSathaye
section
variable {B : Type*} [CommRing B]

theorem substitute_S (h U G W : B) :
    S h U (G-U*W) W =
      h*G^2 - 2*U*(h*W-U^2)*G + (h*W-U^2)^2*W := by
  unfold S
  ring

theorem compatibility_identity (h y s U G : B) :
    y^2*(y+U^2) - h*(s-h*G^2+2*U*y*G) =
      (h*G-y*U)^2 + y^3 - h*s := by ring

theorem compatibility (h x y s U G : B)
    (hc : x^2+y^3 = h*s) (hl : h*G-y*U = x) :
    y^2*(y+U^2) = h*(s-h*G^2+2*U*y*G) := by
  apply sub_eq_zero.mp
  rw [compatibility_identity, hl, hc, sub_self]

theorem squared_bezout (h y α β : B) (hb : α*h+β*y = 1) :
    α*(1+β*y)*h + β^2*y^2 = 1 := by
  calc
    _ = (α*h+β*y-1)*(1+β*y)+1 := by ring
    _ = 1 := by rw [hb]; ring

theorem solve_h (h c a b r q : B) (hc : c*a = h*b) (hb : r*h+q*c = 1) :
    h*(r*a+q*b) = a := by
  calc
    _ = r*h*a+q*(h*b) := by ring
    _ = (r*h+q*c)*a := by rw [← hc]; ring
    _ = a := by rw [hb, one_mul]

theorem solve_c (h c a b r q : B) (hc : c*a = h*b) (hb : r*h+q*c = 1) :
    c*(r*a+q*b) = b := by
  calc
    _ = r*(c*a)+q*c*b := by ring
    _ = (r*h+q*c)*b := by rw [hc]; ring
    _ = b := by rw [hb, one_mul]

theorem solve_unique (h c a b r q W : B) (hb : r*h+q*c = 1)
    (hh : h*W = a) (hy : c*W = b) : W = r*a+q*b := by
  calc
    W = (r*h+q*c)*W := by rw [hb, one_mul]
    _ = r*(h*W)+q*(c*W) := by ring
    _ = r*a+q*b := by rw [hh, hy]

theorem linear_parameter_relation (h x y α β T : B) (hb : α*h+β*y = 1) :
    h*(y*T+α*x)-y*(h*T-β*x) = x := by
  calc
    _ = (α*h+β*y)*x := by ring
    _ = x := by rw [hb, one_mul]

theorem linear_parameter_inverse (h x y α β T : B) (hb : α*h+β*y = 1) :
    α*(h*T-β*x)+β*(y*T+α*x) = T := by
  calc
    _ = (α*h+β*y)*T := by ring
    _ = T := by rw [hb, one_mul]

theorem recover_U (h x y α β U G : B)
    (hb : α*h+β*y = 1) (hl : h*G-y*U = x) :
    h*(α*U+β*G)-β*x = U := by
  calc
    _ = (α*h+β*y)*U+β*(h*G-y*U-x) := by ring
    _ = U := by rw [hb, hl]; ring

theorem recover_G (h x y α β U G : B)
    (hb : α*h+β*y = 1) (hl : h*G-y*U = x) :
    y*(α*U+β*G)+α*x = G := by
  calc
    _ = (α*h+β*y)*G-α*(h*G-y*U-x) := by ring
    _ = G := by rw [hb, hl]; ring

theorem original_to_linear (h x y s U V W : B)
    (hx : U^3+h*V = x) (hy : -U^2+h*W = y) (hs : S h U V W = s) :
    h*(V+U*W)-y*U = x ∧ h*W = y+U^2 ∧
      y^2*W = s-h*(V+U*W)^2+2*U*y*(V+U*W) := by
  have hw : h*W-U^2 = y := by rw [← hy]; ring
  have hS : S h U V W =
      h*(V+U*W)^2-2*U*y*(V+U*W)+y^2*W := by
    have hh := substitute_S h U (V+U*W) W
    have hv : V+U*W-U*W = V := by ring
    rw [hv, hw] at hh
    exact hh
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = U^3+h*V+U*(h*W-U^2-y) := by ring
      _ = x := by rw [hw, hx]; ring
  · rw [← hw]; ring
  · rw [← hs, hS]; ring

theorem linear_to_original (h x y s U G W : B)
    (hl : h*G-y*U = x) (hw : h*W = y+U^2)
    (hs : y^2*W = s-h*G^2+2*U*y*G) :
    U^3+h*(G-U*W) = x ∧ -U^2+h*W = y ∧ S h U (G-U*W) W = s := by
  have hh : h*W-U^2 = y := by rw [hw]; ring
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = h*G-y*U-U*(h*W-U^2-y) := by ring
      _ = x := by rw [hl, hh]; ring
  · rw [hw]; ring
  · rw [substitute_S, hh, hs]; ring

end
end AbhyankarSathaye

end OAI


