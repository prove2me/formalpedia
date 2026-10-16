-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
-- name    : OAI_RepresentationTheory_FoulkesHowe_Spanning
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:25:16.652635+00:00
-- url     : https://prove2.me/theorems/4c0eb404-cec7-4b43-bf2f-552a7d370b2e
-- title:
--   Products span $\mathrm{Sym}^n V$, so linear maps out of it are determined on products
-- statement:
--   Let $V$ be a complex vector space, $S(V)$ its symmetric algebra over $\mathbb{C}$, $n\in\mathbb{N}$, and let $\mathrm{Sym}^n V\subseteq S(V)$ be the linear span of the products $[v_0,\dots,v_{n-1}]=v_0v_1\cdots v_{n-1}$ with $v_i\in V$, now regarded as a vector space in its own right.
--
--   1. The products span $\mathrm{Sym}^n V$:
--   $$\operatorname{span}_{\mathbb{C}}\bigl\{[v_0,\dots,v_{n-1}]\ :\ v_0,\dots,v_{n-1}\in V\bigr\}=\mathrm{Sym}^n V.$$
--   2. If $W$ is a complex vector space and $f,g:\mathrm{Sym}^n V\to W$ are linear maps with $f([v_0,\dots,v_{n-1}])=g([v_0,\dots,v_{n-1}])$ for all $v_0,\dots,v_{n-1}\in V$, then $f=g$.
--
--   This extensionality principle is used whenever two linear maps out of a symmetric power, or out of an iterated symmetric power, have to be compared, for example to show that a linear map is uniquely determined by a prescribed formula on products.
--
--   **Formalization Note** Item 1 is a statement about the subtype `SymPow n V` of the symmetric algebra: the span of the range of `symMonomial n V` inside this subtype is the whole space. The two items are `span_symMonomial` and `symPow_linearMap_ext`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Spanning.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Spanning.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear

namespace OAI

noncomputable section
open scoped BigOperators
universe u v
namespace Problem346

/-- Monomials span the symmetric power, in its subtype realization. -/
theorem span_symMonomial (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    Submodule.span ℂ (Set.range (symMonomial n V)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (symPowSubmodule n V)
    (fun x => Submodule.subset_span (Set.mem_range_self x))).2
  rfl

/-- Maps out of a symmetric power are determined by monomials. -/
theorem symPow_linearMap_ext (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    {W : Type v} [AddCommGroup W] [Module ℂ W]
    (f g : SymPow n V →ₗ[ℂ] W)
    (h : ∀ x : Fin n → V, f (symMonomial n V x) = g (symMonomial n V x)) : f = g := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top f g (span_symMonomial n V)).2
  rintro ⟨_, x, rfl⟩
  exact h x

end Problem346

end

end OAI


