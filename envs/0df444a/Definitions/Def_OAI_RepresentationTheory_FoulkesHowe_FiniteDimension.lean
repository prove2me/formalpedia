-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
-- name    : OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:21:55.746277+00:00
-- url     : https://prove2.me/theorems/04d92e1b-3274-4df4-b14c-a7693e751e98
-- title:
--   Symmetric powers of a finite-dimensional complex vector space are finite-dimensional
-- statement:
--   Let $V$ be a finite-dimensional complex vector space and $S(V)$ its symmetric algebra over $\mathbb{C}$. For $n\in\mathbb{N}$ let $\mathrm{Sym}^n V\subseteq S(V)$ be the linear span of all products $v_0v_1\cdots v_{n-1}$ of $n$ vectors $v_i\in V$. Then for every $n\in\mathbb{N}$
--   $$\dim_{\mathbb{C}}\mathrm{Sym}^n V<\infty .$$
--
--   Applying the statement twice shows that plethysms $\mathrm{Sym}^a(\mathrm{Sym}^b V)$ of a finite-dimensional space are finite-dimensional, so that dimension counts and the identification of a finite-dimensional space with its double dual are available for them.
--
--   **Formalization Note** The result is registered as a typeclass instance `finiteDimensional_symPow`, so finite-dimensionality of `SymPow n V`, and of iterated symmetric powers such as `SymPow a (SymPow b V)`, is inferred automatically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/FiniteDimension.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/FiniteDimension.lean by skeleton subtraction
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

namespace OAI

noncomputable section
universe u

namespace Problem346

/-- Every homogeneous symmetric power of a finite-dimensional complex space is
finite dimensional. The proof uses its tensor-power presentation. -/
instance finiteDimensional_symPow (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] : FiniteDimensional ℂ (SymPow n V) :=
  Module.Finite.of_surjective (tensorToSymPow n V) (tensorToSymPow_surjective n V)

end Problem346

end

end OAI


