-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:25:44.229148+00:00
-- url     : https://prove2.me/theorems/2df5125d-d131-4e19-962f-bad8e35d14eb
-- title:
--   Lifting a cusp relation: a three-relation quotient that is a polynomial algebra in one variable
-- statement:
--   Let $B$ be a commutative ring, let $h,x,y,s\in B$, and let $S(h,u,v,w)=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$.
--
--   1. **Lifting quotient.** In the polynomial ring $B[U,V,W]$ consider the relations $U^3+hV-x$, $-U^2+hW-y$ and $S(h,U,V,W)-s$, and the $B$-algebra
--   $$Q(h,x,y,s)=B[U,V,W]\big/\bigl(U^3+hV-x,\ -U^2+hW-y,\ S(h,U,V,W)-s\bigr).$$
--   Writing $U,V,W$ also for the classes of the variables and $h,x,y,s$ for their images under the structure map, $Q(h,x,y,s)$ satisfies $U^3+hV=x$, $-U^2+hW=y$ and $S(h,U,V,W)=s$.
--   2. **Polynomial solution.** For $\alpha,\beta\in B$ define the polynomials in one variable $T$ over $B$
--   $$U(T)=hT-\beta x,\qquad G(T)=yT+\alpha x,\qquad W(T)=\alpha(1+\beta y)\bigl(y+U(T)^2\bigr)+\beta^2\bigl(s-hG(T)^2+2\,U(T)\,y\,G(T)\bigr),$$
--   and $V(T)=G(T)-U(T)W(T)$. If $x^2+y^3=hs$ and $\alpha h+\beta y=1$, then substituting $(U(T),V(T),W(T))$ for $(U,V,W)$ makes all three relations vanish.
--   3. **The isomorphism.** Assume $x^2+y^3=hs$ and $\alpha h+\beta y=1$. The $B$-algebra homomorphisms
--   $$\Phi:Q(h,x,y,s)\to B[T],\quad (U,V,W)\mapsto\bigl(U(T),V(T),W(T)\bigr),\qquad \Psi:B[T]\to Q(h,x,y,s),\quad T\mapsto \alpha U+\beta(V+UW),$$
--   are mutually inverse, so
--   $$Q(h,x,y,s)\cong B[T]\quad\text{as }B\text{-algebras}.$$
--
--   This is the key lifting step of the construction: over any base ring in which the cusp relation $x^2+y^3=hs$ holds and $h,y$ generate the unit ideal, adjoining the three unknowns $U,V,W$ subject to the three equations has the same effect as adjoining one free variable. No assumption such as being a domain is made, so the statement covers the zero ring and rings with zero divisors.
--
--   **Formalization Note** The variables $U,V,W$ are `X 0, X 1, X 2` of `MvPolynomial (Fin 3) B`; the relations are `relX`, `relY`, `relS`, the ideal is `ideal`, the quotient is `Q` with quotient map `qmap` and generators `qvar`, and item 1 is `quotient_relations`. The polynomials are `polyU`, `polyG`, `polyW`, `polyV` (collected in `values`) and item 2 is `values_relations`. Item 3 consists of `forward` (which takes both hypotheses), `backward` (which needs none), the evaluation lemma `forward_qvar`, `forward_backward`, `backward_forward` and the algebra equivalence `equivalence`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Lifting.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Lifting.lean by skeleton subtraction
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

namespace OAI

/-!
# Lifting a cusp relation

If `x² + y³ = h * s` and `α * h + β * y = 1`, the quotient defined by
`U³ + h * V = x`, `-U² + h * W = y`, and `S h U V W = s` is a polynomial
algebra in one variable. This includes the zero ring and rings with zero divisors.
-/

noncomputable section
namespace AbhyankarSathaye.Lifting
open MvPolynomial

variable {B : Type*} [CommRing B]

def relX (h x : B) : MvPolynomial (Fin 3) B := X 0^3+C h*X 1-C x
def relY (h y : B) : MvPolynomial (Fin 3) B := -X 0^2+C h*X 2-C y
def relS (h s : B) : MvPolynomial (Fin 3) B := S (C h) (X 0) (X 1) (X 2)-C s
def ideal (h x y s : B) : Ideal (MvPolynomial (Fin 3) B) :=
  Ideal.span {relX h x, relY h y, relS h s}
abbrev Q (h x y s : B) := MvPolynomial (Fin 3) B ⧸ ideal h x y s
def qmap (h x y s : B) : MvPolynomial (Fin 3) B →ₐ[B] Q h x y s :=
  Ideal.Quotient.mkₐ B (ideal h x y s)
def qvar (h x y s : B) (i : Fin 3) : Q h x y s := qmap h x y s (X i)

theorem quotient_relations (h x y s : B) :
    let c := algebraMap B (Q h x y s)
    let U := qvar h x y s 0
    let V := qvar h x y s 1
    let W := qvar h x y s 2
    U^3+c h*V = c x ∧ -U^2+c h*W = c y ∧ S (c h) U V W = c s := by
  dsimp only
  have hx : qmap h x y s (relX h x) = 0 :=
    quotient_triple_first (relX h x) (relY h y) (relS h s)
  have hy : qmap h x y s (relY h y) = 0 :=
    quotient_triple_second (relX h x) (relY h y) (relS h s)
  have hs : qmap h x y s (relS h s) = 0 :=
    quotient_triple_third (relX h x) (relY h y) (relS h s)
  refine ⟨?_, ?_, ?_⟩
  · apply sub_eq_zero.mp
    simpa [relX, qvar] using hx
  · apply sub_eq_zero.mp
    simpa [relY, qvar] using hy
  · apply sub_eq_zero.mp
    simpa [relS, qvar] using hs

def polyU (h x β : B) : Polynomial B := inverseU (Polynomial.C h) (Polynomial.C x)
  (Polynomial.C β) Polynomial.X
def polyG (x y α : B) : Polynomial B := inverseG (Polynomial.C x) (Polynomial.C y)
  (Polynomial.C α) Polynomial.X
def polyW (h x y s α β : B) : Polynomial B :=
  inverseW (Polynomial.C h) (Polynomial.C y) (Polynomial.C s) (Polynomial.C α)
    (Polynomial.C β) (polyU h x β) (polyG x y α)
def polyV (h x y s α β : B) : Polynomial B :=
  inverseV (polyU h x β) (polyG x y α) (polyW h x y s α β)
def values (h x y s α β : B) : Fin 3 → Polynomial B :=
  ![polyU h x β, polyV h x y s α β, polyW h x y s α β]

theorem values_relations (h x y s α β : B)
    (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    (aeval (values h x y s α β)) (relX h x) = 0 ∧
    (aeval (values h x y s α β)) (relY h y) = 0 ∧
    (aeval (values h x y s α β)) (relS h s) = 0 := by
  have hc' : (Polynomial.C x)^2+(Polynomial.C y)^3 = Polynomial.C h*Polynomial.C s := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hc
  have hb' : Polynomial.C α*Polynomial.C h+Polynomial.C β*Polynomial.C y = 1 := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hb
  have hr := inverse_relations (Polynomial.C h) (Polynomial.C x) (Polynomial.C y)
    (Polynomial.C s) (Polynomial.C α) (Polynomial.C β) Polynomial.X hc' hb'
  dsimp only at hr
  refine ⟨?_, ?_, ?_⟩
  · simpa [relX, values, polyU, polyV, polyG, polyW, Polynomial.algebraMap_eq]
      using sub_eq_zero.mpr hr.1
  · simpa [relY, values, polyU, polyV, polyG, polyW, Polynomial.algebraMap_eq]
      using sub_eq_zero.mpr hr.2.1
  · simpa [relS, values, polyU, polyV, polyG, polyW, Polynomial.algebraMap_eq]
      using sub_eq_zero.mpr hr.2.2

def forward (h x y s α β : B) (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    Q h x y s →ₐ[B] Polynomial B :=
  lift_triple (relX h x) (relY h y) (relS h s) (aeval (values h x y s α β))
    (values_relations h x y s α β hc hb).1
    (values_relations h x y s α β hc hb).2.1
    (values_relations h x y s α β hc hb).2.2

@[simp] theorem forward_qvar (h x y s α β : B) (hc hb) (i : Fin 3) :
    forward h x y s α β hc hb (qvar h x y s i) = values h x y s α β i := by
  change aeval (values h x y s α β) (X i) = values h x y s α β i
  exact aeval_X _ _

def backward (h x y s α β : B) : Polynomial B →ₐ[B] Q h x y s :=
  Polynomial.aeval (parameter (algebraMap B _ α) (algebraMap B _ β)
    (qvar h x y s 0) (qvar h x y s 1) (qvar h x y s 2))

theorem forward_backward (h x y s α β : B) (hc hb) :
    (forward h x y s α β hc hb).comp (backward h x y s α β) = AlgHom.id B _ := by
  apply Polynomial.algHom_ext
  have hb' : Polynomial.C α*Polynomial.C h+Polynomial.C β*Polynomial.C y = 1 := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hb
  simpa [backward, values, polyU, polyV, polyW, polyG, Polynomial.algebraMap_eq]
    using inverse_parameter (Polynomial.C h) (Polynomial.C x) (Polynomial.C y)
      (Polynomial.C s) (Polynomial.C α) (Polynomial.C β) Polynomial.X hb'

theorem backward_forward (h x y s α β : B) (hc hb) :
    (backward h x y s α β).comp (forward h x y s α β hc hb) = AlgHom.id B _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hb' : algebraMap B (Q h x y s) α*algebraMap B _ h+
      algebraMap B _ β*algebraMap B _ y = 1 := by
    simpa using congrArg (algebraMap B (Q h x y s)) hb
  obtain ⟨hx, hy, hs⟩ := quotient_relations h x y s
  have hr := original_reconstruction (algebraMap B (Q h x y s) h)
    (algebraMap B _ x) (algebraMap B _ y) (algebraMap B _ s)
    (algebraMap B _ α) (algebraMap B _ β)
    (qvar h x y s 0) (qvar h x y s 1) (qvar h x y s 2) hb' hx hy hs
  dsimp only at hr
  change backward h x y s α β (forward h x y s α β hc hb (qvar h x y s i)) =
    qvar h x y s i
  rw [forward_qvar]
  fin_cases i
  · simpa [values, polyU, backward] using hr.1
  · simpa [values, polyU, polyV, polyG, polyW, backward] using hr.2.1
  · simpa [values, polyU, polyV, polyG, polyW, backward] using hr.2.2

def equivalence (h x y s α β : B) (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    Q h x y s ≃ₐ[B] Polynomial B :=
  AlgEquiv.ofAlgHom (forward h x y s α β hc hb) (backward h x y s α β)
    (forward_backward h x y s α β hc hb) (backward_forward h x y s α β hc hb)

end AbhyankarSathaye.Lifting

end

end OAI


