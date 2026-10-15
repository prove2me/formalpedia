-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:28:49.120027+00:00
-- url     : https://prove2.me/theorems/88fe6051-feaf-46b2-a22b-ed8049218c3c
-- title:
--   Lifting quotient of a cusp relation and its explicit one-parameter solution
-- statement:
--   Let $B$ be an arbitrary commutative ring (the zero ring and rings with zero divisors are allowed), and let
--
--   $$
--   S(h,u,v,w)=2u^3v+3u^4w+h\,(v^2-3u^2w^2)+h^2w^3 .
--   $$
--
--   For elements $h,x,y,s\in B$ the file introduces the following objects.
--
--   1. **Lifting quotient.** In the polynomial ring $B[U,V,W]$ consider the three relations
--
--      $$\rho_x=U^3+hV-x,\qquad \rho_y=-U^2+hW-y,\qquad \rho_s=S(h,U,V,W)-s,$$
--
--      the ideal $I_{h,x,y,s}=(\rho_x,\rho_y,\rho_s)$, the quotient $B$-algebra $Q_{h,x,y,s}=B[U,V,W]/I_{h,x,y,s}$ with its quotient map, and the classes $\bar U,\bar V,\bar W$ of the three variables. For all $h,x,y,s$ one has, in $Q_{h,x,y,s}$,
--
--      $$\bar U^3+h\bar V=x,\qquad -\bar U^2+h\bar W=y,\qquad S(h,\bar U,\bar V,\bar W)=s .$$
--
--   2. **Explicit one-parameter solution.** For further elements $\alpha,\beta\in B$ define the following polynomials in one variable $T$ over $B$:
--
--      $$U(T)=hT-\beta x,\qquad G(T)=yT+\alpha x,$$
--
--      $$W(T)=\alpha(1+\beta y)\bigl(y+U(T)^2\bigr)+\beta^2\bigl(s-h\,G(T)^2+2y\,U(T)\,G(T)\bigr),\qquad V(T)=G(T)-U(T)\,W(T).$$
--
--      If $x^2+y^3=hs$ and $\alpha h+\beta y=1$, then $(U(T),V(T),W(T))$ is a common zero of $\rho_x,\rho_y,\rho_s$ in $B[T]$.
--
--   3. **Forward map.** Under the same two hypotheses, $\Phi_{\alpha,\beta}:Q_{h,x,y,s}\to B[T]$ is the $B$-algebra homomorphism with $\bar U\mapsto U(T)$, $\bar V\mapsto V(T)$ and $\bar W\mapsto W(T)$.
--
--   The hypothesis $x^2+y^3=hs$ says that $(x,y)$ satisfies a cusp relation divisible by $h$, and $\alpha h+\beta y=1$ is a Bézout certificate that $h$ and $y$ generate the unit ideal. Under these hypotheses $\Phi_{\alpha,\beta}$ is an isomorphism whose inverse sends $T$ to $\alpha\bar U+\beta(\bar V+\bar U\bar W)$ (shown in accompanying results), so the lifting quotient is a polynomial algebra in one variable over $B$. In the study of the hypersurface $F=0$ in $\mathbb{C}^4$, this is the step that recovers the variables $u,v,w$ over the coordinate ring of the plane presentation.
--
--   **Formalization Note** The variables $U,V,W$ are `X 0`, `X 1`, `X 2` of `MvPolynomial (Fin 3) B`. Lean names: `relX`, `relY`, `relS`, `ideal`, `Q`, `qmap`, `qvar`, and the lemma `quotient_relations` for item 1; `polyU`, `polyG`, `polyW`, `polyV` (the generic formulas `inverseU`, `inverseG`, `inverseW`, `inverseV` evaluated with constant coefficients), `values` and the lemma `values_relations` for item 2; `forward`, which takes the two hypotheses as arguments, with the simp lemma `forward_qvar` for item 3.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Lifting.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Lifting.lean by skeleton subtraction
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

end AbhyankarSathaye.Lifting

end

end OAI


