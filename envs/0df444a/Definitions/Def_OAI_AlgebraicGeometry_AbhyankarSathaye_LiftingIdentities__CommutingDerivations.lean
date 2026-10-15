-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:25:05.046811+00:00
-- url     : https://prove2.me/theorems/eba23147-af9a-4b49-ae1f-c29e31be0650
-- title:
--   Linearizing the lifting equations $U^3+hV=x$, $-U^2+hW=y$, $S(h,U,V,W)=s$
-- statement:
--   All statements hold for elements of an arbitrary commutative ring $B$, where $S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$. They concern the *lifting system*
--   $$U^3+hV=x,\qquad -U^2+hW=y,\qquad S(h,U,V,W)=s$$
--   in the unknowns $U,V,W$ for given $h,x,y,s$, together with the substitution $G=V+UW$.
--
--   1. **Substitution.** $S(h,U,G-UW,W)=hG^2-2U(hW-U^2)G+(hW-U^2)^2W$.
--   2. **Compatibility.** The identity $y^2(y+U^2)-h\,(s-hG^2+2UyG)=(hG-yU)^2+y^3-hs$ holds. Consequently, if $x^2+y^3=hs$ and $hG-yU=x$, then $y^2(y+U^2)=h\,(s-hG^2+2UyG)$.
--   3. **Squared Bézout relation.** If $\alpha h+\beta y=1$, then $\alpha(1+\beta y)\,h+\beta^2y^2=1$.
--   4. **Solving $hW=a$, $cW=b$.** If $ca=hb$ and $rh+qc=1$, then $W=ra+qb$ satisfies $hW=a$ and $cW=b$. If $rh+qc=1$, then every $W$ with $hW=a$ and $cW=b$ equals $ra+qb$.
--   5. **The free parameter.** If $\alpha h+\beta y=1$, then for every $T$,
--      $$h(yT+\alpha x)-y(hT-\beta x)=x,\qquad \alpha(hT-\beta x)+\beta(yT+\alpha x)=T .$$
--   6. **Recovering $U$ and $G$.** If $\alpha h+\beta y=1$ and $hG-yU=x$, then $h(\alpha U+\beta G)-\beta x=U$ and $y(\alpha U+\beta G)+\alpha x=G$.
--   7. **Equivalence with a linear system.** If $(U,V,W)$ solves the lifting system, then $G=V+UW$ satisfies
--      $$hG-yU=x,\qquad hW=y+U^2,\qquad y^2W=s-hG^2+2UyG .$$
--      Conversely, if $(U,G,W)$ satisfies these three equations, then $(U,\,G-UW,\,W)$ solves the lifting system.
--
--   After the substitution, the system becomes one linear equation $hG-yU=x$ for the pair $(U,G)$. Once that pair is fixed, two linear equations for $W$ remain, and item 2 shows they are compatible when $x^2+y^3=hs$. When $h$ and $y$ are comaximal, item 5 parametrizes the solutions $(U,G)$ by a single element $T$. Items 3 and 4 then determine $W$ uniquely, using $c=y^2$, $a=y+U^2$, $b=s-hG^2+2UyG$, $r=\alpha(1+\beta y)$ and $q=\beta^2$. No cancellation is used anywhere, so the identities hold over every commutative ring. They are assembled into explicit inverse formulas in the reconstruction file.
--
--   **Formalization Note** The items are the theorems `substitute_S`, `compatibility_identity` and `compatibility`, `squared_bezout`, `solve_h`, `solve_c` and `solve_unique`, `linear_parameter_relation` and `linear_parameter_inverse`, `recover_U` and `recover_G`, and `original_to_linear` and `linear_to_original`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/LiftingIdentities.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/LiftingIdentities.lean by skeleton subtraction
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


