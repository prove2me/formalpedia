-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
-- name    : OAI_Analysis_ProductSpaces_ClosedTails
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:09:51.863233+00:00
-- url     : https://prove2.me/theorems/c3803d7e-8ec5-40e7-a283-ccd0eca36b3f
-- title:
--   Head spans and closed tail subspaces of the $L^1$ product span
-- statement:
--   Let $\mu$ be a Borel probability measure on $\mathbb R$ with $\int w^2\,d\mu<\infty$. Let $X_\mu$ be the closed linear span in $L^1(\mathbb P_\mu)$ of the path products $\pi_v$, where $v$ ranges over the tree of finite sequences of positive integers and $\mathbb P_\mu$ is the product of independent copies of $\mu$ over the nonroot vertices, and write $P_v\in X_\mu$ for the class of $\pi_v$. Fix a finite head $T$, i.e. a finite prefix-closed set of vertices containing the root, and let $\operatorname{anc}_T(v)$ be the last vertex of $T$ on the path from the root to $v$ (so $\operatorname{anc}_T(v)=v$ for $v\in T$).
--
--   1. **Head span.** $H_T=\operatorname{span}\{P_v:\ v\in T\}\subseteq X_\mu$; it is finite-dimensional.
--
--   2. **Relative vectors.** For a vertex $v$, $R_T(v)=P_v-P_{\operatorname{anc}_T(v)}$, the increment of the path vector from the last head ancestor of $v$ to $v$ (it vanishes for $v\in T$).
--
--   3. **Algebraic tail.** $\operatorname{Tail}^{\mathrm{alg}}_T=\operatorname{span}\{R_T(v):\ v\notin T\}$.
--
--   4. **Closed tail space.** $\operatorname{Tail}_T=\overline{\operatorname{Tail}^{\mathrm{alg}}_T}$, the closure of the algebraic tail in $X_\mu$.
--
--   Every path vector decomposes as $P_v=R_T(v)+P_{\operatorname{anc}_T(v)}$, with the first term in the tail and the second in the head span; consequently $\operatorname{Tail}_T$ is a closed subspace of finite codimension in $X_\mu$. These are the subspaces on which asymptotic midpoint estimates are tested: a centre in the head span is compared with directions taken from the closed tail.
--
--   **Formalization Note** The Lean definitions are `FiniteHead.headSpan`, `FiniteHead.relativeVector`, `FiniteHead.tailAlgebraic` and `FiniteHead.tailSpace` (a `Submodule.topologicalClosure`), all depending on the second-moment hypothesis `h₂` through `pathVector`; finite-dimensionality of the head span is the instance `headSpan_finiteDimensional`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ClosedTails.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ClosedTails.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts
section Tails
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)

namespace FiniteHead
variable (T : FiniteHead)

def headSpan : Submodule ℝ (productSpan μ) :=
  Submodule.span ℝ (pathVector μ h₂ '' (T.vertices : Set Vertex))

instance headSpan_finiteDimensional : FiniteDimensional ℝ (T.headSpan μ h₂) :=
  FiniteDimensional.span_of_finite ℝ (T.vertices.finite_toSet.image _)

/-- Relative tail products, algebraically equal to sums of outside-head jumps. -/
def relativeVector (v : Vertex) : productSpan μ :=
  pathVector μ h₂ v - pathVector μ h₂ (T.ancestor v)

def tailAlgebraic : Submodule ℝ (productSpan μ) :=
  Submodule.span ℝ (T.relativeVector μ h₂ '' {v : Vertex | v ∉ T.vertices})

def tailSpace : Submodule ℝ (productSpan μ) := (T.tailAlgebraic μ h₂).topologicalClosure

end FiniteHead
end Tails
end IndependentProducts

end

end OAI


