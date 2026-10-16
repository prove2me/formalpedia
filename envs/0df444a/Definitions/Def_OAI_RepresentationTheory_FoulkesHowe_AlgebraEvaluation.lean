-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
-- name    : OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:19:21.390754+00:00
-- url     : https://prove2.me/theorems/5130d751-9ec3-4866-880f-c23b9f4261e1
-- title:
--   Point evaluations separate the symmetric algebra of a complex vector space
-- statement:
--   Let $W$ be a complex vector space, $W^*=\mathrm{Hom}_{\mathbb{C}}(W,\mathbb{C})$ its dual space, and $S(W)$ its symmetric algebra over $\mathbb{C}$. Every linear functional $\varphi\in W^*$ extends uniquely to a $\mathbb{C}$-algebra homomorphism $\mathrm{ev}_\varphi:S(W)\to\mathbb{C}$. After a choice of basis $(e_k)$ of $W$, $S(W)$ is a polynomial ring in variables $X_k$ corresponding to the $e_k$, and $\mathrm{ev}_\varphi(p)$ is the value of the polynomial $p$ at the point $X_k=\varphi(e_k)$.
--
--   1. For every complex vector space $W$, of any dimension, and every $p\in S(W)$:
--   $$\bigl(\mathrm{ev}_\varphi(p)=0\ \text{ for all }\varphi\in W^*\bigr)\ \Longrightarrow\ p=0.$$
--   2. If $W$ is finite-dimensional, then for every $p\in S(W^*)$: if $\mathrm{ev}_{\hat x}(p)=0$ for every $x\in W$, where $\hat x\in W^{**}$ is evaluation at $x$, $\hat x(\varphi)=\varphi(x)$, then $p=0$.
--
--   In the language of polynomial functions, item 2 says that an element of $S(W^*)$, viewed as a polynomial function on $W$, is zero as soon as it vanishes at every point of $W$. It is the input for proving that duality maps $\mathrm{Sym}^n(W^*)\to(\mathrm{Sym}^n W)^*$ are injective by testing them on pure powers $x^n$.
--
--   **Formalization Note** The homomorphism $\mathrm{ev}_\varphi$ is `SymmetricAlgebra.lift φ`, and $\hat x$ is `Module.Dual.eval` applied to `x`; the two statements are `symAlg_eq_zero_of_lift_eq_zero` and `symAlg_dual_eq_zero_of_eval_eq_zero`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/AlgebraEvaluation.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/AlgebraEvaluation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift

namespace OAI

noncomputable section

universe u
namespace Problem346

variable (W : Type u) [AddCommGroup W] [Module ℂ W]

/-- Linear functionals separate points of the symmetric algebra over an infinite field. -/
theorem symAlg_eq_zero_of_lift_eq_zero (p : SymmetricAlgebra ℂ W)
    (h : ∀ φ : Module.Dual ℂ W, SymmetricAlgebra.lift φ p = 0) : p = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let e := SymmetricAlgebra.equivMvPolynomial b
  apply e.injective
  simp only [map_zero]
  apply MvPolynomial.funext
  intro x
  have he : (MvPolynomial.aeval x).comp e.toAlgHom =
      SymmetricAlgebra.lift (b.constr ℂ x) := by
    apply SymmetricAlgebra.algHom_ext
    apply b.ext
    intro i
    simp [e]
  have hx := congrArg (fun f : SymmetricAlgebra ℂ W →ₐ[ℂ] ℂ => f p) he
  simpa using hx.trans (h (b.constr ℂ x))

/-- Evaluation at vectors separates the symmetric algebra on the dual of a finite-dimensional
space. -/
theorem symAlg_dual_eq_zero_of_eval_eq_zero [FiniteDimensional ℂ W]
    (p : SymmetricAlgebra ℂ (Module.Dual ℂ W))
    (h : ∀ x : W, SymmetricAlgebra.lift (Module.Dual.eval ℂ W x) p = 0) : p = 0 := by
  apply symAlg_eq_zero_of_lift_eq_zero
  intro φ
  obtain ⟨x, rfl⟩ := (Module.evalEquiv ℂ W).surjective φ
  exact h x

end Problem346

end

end OAI


