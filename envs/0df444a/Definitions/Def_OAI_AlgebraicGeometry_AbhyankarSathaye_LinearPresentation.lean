-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LinearPresentation
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_LinearPresentation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:30:28.875844+00:00
-- url     : https://prove2.me/theorems/1126d3ac-1dfa-41a3-8ba3-b3bdf94fd4a5
-- title:
--   The linear relation $hG-yU=x$ and its one-parameter solution
-- statement:
--   Let $B$ be a commutative ring and $h,x,y\in B$.
--
--   1. **Linear presentation.** In the polynomial ring $B[U,G]$ in two variables take the single relation $hG-yU-x$ and form the $B$-algebra
--   $$A(h,x,y)=B[U,G]\big/\bigl(hG-yU-x\bigr),$$
--   together with its quotient map and the classes $U,G$ of the two variables.
--   2. **Parametrization.** For $\alpha,\beta\in B$ consider the pair of polynomials $U(T)=hT-\beta x$ and $G(T)=yT+\alpha x$ in $B[T]$.
--   3. **Forward map.** If $\alpha h+\beta y=1$, there is a $B$-algebra homomorphism
--   $$A(h,x,y)\to B[T],\qquad U\mapsto hT-\beta x,\quad G\mapsto yT+\alpha x,$$
--   which is well defined because $h(yT+\alpha x)-y(hT-\beta x)=(\alpha h+\beta y)\,x=x$.
--
--   After the substitution $G=V+UW$, and given $-U^2+hW=y$, the first lifting equation $U^3+hV=x$ becomes the linear relation $hG-yU=x$. The algebra $A(h,x,y)$ is therefore the intermediate stage of the lifting construction in which only this relation is imposed, and the forward map realizes its solutions as the line $T\mapsto(hT-\beta x,\ yT+\alpha x)$, whose parameter is recovered as $T=\alpha U+\beta G$.
--
--   **Formalization Note** The variables $U,G$ are `X 0, X 1` of `MvPolynomial (Fin 2) B`; the objects are `relation`, `ideal`, `A`, `qmap`, `qvar`, `values` (the pair `Lifting.polyU h x β`, `Lifting.polyG x y α`), `forward` (which takes the hypothesis $\alpha h+\beta y=1$) and its evaluation lemma `forward_qvar`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/LinearPresentation.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/LinearPresentation.lean by skeleton subtraction
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

namespace OAI

/-!
# The intermediate linear presentation

The relation `h * G - y * U = x` has parameter `α * U + β * G`.
The remaining compatible equations generate the principal ideal `(W - W₀)`.
-/

noncomputable section
namespace AbhyankarSathaye.LinearPresentation
open MvPolynomial

variable {B : Type*} [CommRing B]

def relation (h x y : B) : MvPolynomial (Fin 2) B := C h*X 1-C y*X 0-C x
def ideal (h x y : B) : Ideal (MvPolynomial (Fin 2) B) := Ideal.span {relation h x y}
abbrev A (h x y : B) := MvPolynomial (Fin 2) B ⧸ ideal h x y
def qmap (h x y : B) : MvPolynomial (Fin 2) B →ₐ[B] A h x y :=
  Ideal.Quotient.mkₐ B (ideal h x y)
def qvar (h x y : B) (i : Fin 2) : A h x y := qmap h x y (X i)
def values (h x y α β : B) : Fin 2 → Polynomial B :=
  ![Lifting.polyU h x β, Lifting.polyG x y α]

def forward (h x y α β : B) (hb : α*h+β*y = 1) : A h x y →ₐ[B] Polynomial B := by
  let ev : MvPolynomial (Fin 2) B →ₐ[B] Polynomial B := aeval (values h x y α β)
  have hb' : Polynomial.C α*Polynomial.C h+Polynomial.C β*Polynomial.C y = 1 := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hb
  have he : ev (relation h x y) = 0 := by
    simpa [ev, values, relation, Lifting.polyU, Lifting.polyG,
      Polynomial.algebraMap_eq, inverseU, inverseG] using
      sub_eq_zero.mpr (linear_parameter_relation (Polynomial.C h) (Polynomial.C x)
        (Polynomial.C y) (Polynomial.C α) (Polynomial.C β) Polynomial.X hb')
  have hi : ideal h x y ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact he
  exact Ideal.Quotient.liftₐ _ ev (fun z hz => hi hz)

@[simp] theorem forward_qvar (h x y α β : B) (hb) (i : Fin 2) :
    forward h x y α β hb (qvar h x y i) = values h x y α β i := by
  change (aeval (values h x y α β) : MvPolynomial (Fin 2) B →ₐ[B] Polynomial B) (X i) = _
  exact aeval_X _ _

end AbhyankarSathaye.LinearPresentation

end

end OAI


