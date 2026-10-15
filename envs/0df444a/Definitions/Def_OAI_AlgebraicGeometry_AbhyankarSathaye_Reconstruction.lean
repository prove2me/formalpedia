-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:25:07.363278+00:00
-- url     : https://prove2.me/theorems/ca2eb913-050e-471b-b96d-28ef60dc5c55
-- title:
--   Mutually inverse polynomial formulas between solutions of the lifting equations and one parameter
-- statement:
--   Let $B$ be a commutative ring, let $h,x,y,s,\alpha,\beta\in B$, and let $S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$. The file defines the polynomial formulas
--   $$U(T)=hT-\beta x,\qquad G(T)=yT+\alpha x,$$
--   $$W(U,G)=\alpha(1+\beta y)(y+U^2)+\beta^2\bigl(s-hG^2+2UyG\bigr),\qquad V(U,G,W)=G-UW,$$
--   and the parameter $\tau(U,V,W)=\alpha U+\beta(V+UW)$. For $T\in B$ abbreviate $U_T=U(T)$, $G_T=G(T)$, $W_T=W(U_T,G_T)$ and $V_T=G_T-U_TW_T$.
--
--   1. **Solutions from a parameter.** If $x^2+y^3=hs$ and $\alpha h+\beta y=1$, then for every $T\in B$,
--   $$U_T^3+hV_T=x,\qquad -U_T^2+hW_T=y,\qquad S(h,U_T,V_T,W_T)=s.$$
--   2. **The parameter is recovered.** If $\alpha h+\beta y=1$, then $\tau(U_T,V_T,W_T)=T$ for every $T\in B$.
--   3. **Solutions are recovered.** If $\alpha h+\beta y=1$ and $U,V,W\in B$ satisfy $U^3+hV=x$, $-U^2+hW=y$ and $S(h,U,V,W)=s$, then for $T=\tau(U,V,W)$ one has $U_T=U$, $V_T=V$ and $W_T=W$.
--   4. **Naturality.** Every ring homomorphism $f$ between commutative rings commutes with the five formulas when all inputs are replaced by their images, e.g. $f(hT-\beta x)=f(h)f(T)-f(\beta)f(x)$.
--
--   Hence, whenever $x^2+y^3=hs$ and $\alpha h+\beta y=1$, the solutions $(U,V,W)$ of the three lifting equations correspond bijectively to the elements $T$ of the ring, through explicit polynomial maps in both directions. Used in the polynomial ring $B[T]$ and in the lifting quotient, this is exactly what is needed to show that the lifting quotient is a polynomial algebra in one variable.
--
--   **Formalization Note** The formulas are `inverseU`, `inverseG`, `inverseW`, `inverseV` and `parameter`; items 1 to 3 are `inverse_relations`, `inverse_parameter` and `original_reconstruction` (stated with `let`-bindings for $U_T$, $G_T$, $W_T$), and item 4 consists of the simp lemmas `map_inverseU`, `map_inverseG`, `map_inverseW`, `map_inverseV` and `map_parameter`, stated for any `RingHomClass`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Reconstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Reconstruction.lean by skeleton subtraction
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


