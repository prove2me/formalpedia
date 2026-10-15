-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:25:30.925233+00:00
-- url     : https://prove2.me/theorems/b45bb879-bc59-4fb5-9bab-ca906665439c
-- title:
--   Explicit inverse formulas between solutions of the lifting system and a free parameter $T$
-- statement:
--   Let $B$ be a commutative ring and let $S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$. For elements $h,x,y,s,\alpha,\beta,T,U,G,V,W$ of $B$ the file defines
--
--   $$U(T)=hT-\beta x,\qquad G(T)=yT+\alpha x,\qquad V(U,G,W)=G-UW,$$
--
--   $$W(U,G)=\alpha(1+\beta y)(y+U^2)+\beta^2\bigl(s-hG^2+2UyG\bigr),\qquad \tau(U,V,W)=\alpha U+\beta\,(V+UW).$$
--
--   All five formulas also depend on the fixed data $h,x,y,s,\alpha,\beta$. The file proves:
--
--   1. **Every $T$ gives a solution.** Suppose $x^2+y^3=hs$ and $\alpha h+\beta y=1$. For every $T$, set $U=U(T)$, $G=G(T)$, $W=W(U,G)$ and $V=G-UW$. Then
--      $$U^3+hV=x,\qquad -U^2+hW=y,\qquad S(h,U,V,W)=s .$$
--   2. **The parameter is recovered.** If $\alpha h+\beta y=1$, these $U,V,W$ satisfy $\tau(U,V,W)=T$.
--   3. **Every solution comes from its parameter.** Suppose $\alpha h+\beta y=1$ and $(U,V,W)$ satisfies the three equations of item 1. Put $T=\tau(U,V,W)$ and $U'=U(T)$, $G'=G(T)$, $W'=W(U',G')$. Then $U'=U$, $G'-U'W'=V$ and $W'=W$.
--   4. **Naturality.** Ring homomorphisms commute with all five formulas.
--
--   So, over a base point $(h,x,y,s)$ on the cusp $x^2+y^3=hs$ with $h$ and $y$ comaximal, the solutions $(U,V,W)$ of the lifting system correspond bijectively, through explicit polynomial formulas, to a single free parameter $T$. In the application, $\mathbb{C}[h,u,v,w]$ is localized at $F+1$ and $\alpha,\beta$ come from the relative Bézout identity. The formulas then express $u,v,w$ as polynomials in $x+s^3$, $y-s^2$ and $T=\alpha u+\beta(v+uw)$ with Laurent coefficients in $F+1$, and conversely. This is what makes the localization a polynomial ring in three variables.
--
--   **Formalization Note** The formulas are `inverseU`, `inverseG`, `inverseW`, `inverseV` and `parameter`. The three items are `inverse_relations`, `inverse_parameter` and `original_reconstruction`. The `map_*` lemmas are the naturality simp lemmas for any `RingHomClass`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Reconstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Reconstruction.lean by skeleton subtraction
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

namespace OAI

/-!
# Mutually inverse polynomial formulas

The parameter `T = α * U + β * (V + U * W)` and the formulas `inverseU`,
`inverseV`, and `inverseW` reconstruct each other over arbitrary commutative rings.
-/

namespace AbhyankarSathaye
section
variable {B : Type*} [CommRing B]

def inverseU (h x β T : B) : B := h*T-β*x
def inverseG (x y α T : B) : B := y*T+α*x
def inverseW (h y s α β U G : B) : B :=
  α*(1+β*y)*(y+U^2)+β^2*(s-h*G^2+2*U*y*G)
def inverseV (U G W : B) : B := G-U*W
def parameter (α β U V W : B) : B := α*U+β*(V+U*W)

theorem inverse_relations (h x y s α β T : B)
    (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    let U := inverseU h x β T
    let G := inverseG x y α T
    let W := inverseW h y s α β U G
    U^3+h*inverseV U G W = x ∧ -U^2+h*W = y ∧ S h U (inverseV U G W) W = s := by
  dsimp only
  have hl := linear_parameter_relation h x y α β T hb
  have hcompat := compatibility h x y s (inverseU h x β T) (inverseG x y α T) hc hl
  have hb2 := squared_bezout h y α β hb
  have hw := solve_h h (y^2) (y+(inverseU h x β T)^2)
    (s-h*(inverseG x y α T)^2+2*(inverseU h x β T)*y*(inverseG x y α T))
    (α*(1+β*y)) (β^2) hcompat hb2
  have hs := solve_c h (y^2) (y+(inverseU h x β T)^2)
    (s-h*(inverseG x y α T)^2+2*(inverseU h x β T)*y*(inverseG x y α T))
    (α*(1+β*y)) (β^2) hcompat hb2
  exact linear_to_original h x y s _ _ _ hl hw hs

theorem inverse_parameter (h x y s α β T : B) (hb : α*h+β*y = 1) :
    let U := inverseU h x β T
    let G := inverseG x y α T
    let W := inverseW h y s α β U G
    parameter α β U (inverseV U G W) W = T := by
  dsimp only [parameter, inverseV]
  have he := linear_parameter_inverse h x y α β T hb
  dsimp [inverseU, inverseG]
  convert he using 1
  ring

theorem original_reconstruction (h x y s α β U V W : B)
    (hb : α*h+β*y = 1) (hx : U^3+h*V = x)
    (hy : -U^2+h*W = y) (hs : S h U V W = s) :
    let T := parameter α β U V W
    let U' := inverseU h x β T
    let G' := inverseG x y α T
    let W' := inverseW h y s α β U' G'
    U' = U ∧ inverseV U' G' W' = V ∧ W' = W := by
  dsimp only
  obtain ⟨hl, hw, hs'⟩ := original_to_linear h x y s U V W hx hy hs
  have hu : inverseU h x β (parameter α β U V W) = U :=
    recover_U h x y α β U (V+U*W) hb hl
  have hg : inverseG x y α (parameter α β U V W) = V+U*W :=
    recover_G h x y α β U (V+U*W) hb hl
  rw [hu, hg]
  have hww : inverseW h y s α β U (V+U*W) = W :=
    (solve_unique h (y^2) (y+U^2) (s-h*(V+U*W)^2+2*U*y*(V+U*W))
      (α*(1+β*y)) (β^2) W (squared_bezout h y α β hb) hw hs').symm
  rw [hww]
  refine ⟨rfl, ?_, rfl⟩
  unfold inverseV
  ring

end

section Maps
variable {B D H : Type*} [CommRing B] [CommRing D]
variable [FunLike H B D] [RingHomClass H B D]

@[simp] theorem map_inverseU (f : H) (h x β T : B) :
    f (inverseU h x β T) = inverseU (f h) (f x) (f β) (f T) := by simp [inverseU]
@[simp] theorem map_inverseG (f : H) (x y α T : B) :
    f (inverseG x y α T) = inverseG (f x) (f y) (f α) (f T) := by simp [inverseG]
@[simp] theorem map_inverseW (f : H) (h y s α β U G : B) :
    f (inverseW h y s α β U G) =
      inverseW (f h) (f y) (f s) (f α) (f β) (f U) (f G) := by simp [inverseW, map_ofNat]
@[simp] theorem map_inverseV (f : H) (U G W : B) :
    f (inverseV U G W) = inverseV (f U) (f G) (f W) := by simp [inverseV]
@[simp] theorem map_parameter (f : H) (α β U V W : B) :
    f (parameter α β U V W) = parameter (f α) (f β) (f U) (f V) (f W) := by
  simp [parameter]

end Maps
end AbhyankarSathaye

end OAI


