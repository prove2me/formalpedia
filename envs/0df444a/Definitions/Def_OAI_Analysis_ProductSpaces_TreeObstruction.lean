-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
-- name    : OAI_Analysis_ProductSpaces_TreeObstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:55:25.079218+00:00
-- url     : https://prove2.me/theorems/9560c5c6-1a60-48d5-ad12-98a5e2270d78
-- title:
--   Children in the positive-integer tree and weakly null sequences
-- statement:
--   Throughout, a vertex of the tree $\mathcal T$ is a finite sequence $v=(v_1,\dots,v_k)$ of positive integers; the root is the empty sequence.
--
--   1. **Children.** For a vertex $v$ and $n\in\mathbb N=\{0,1,2,\dots\}$, the $n$-th child of $v$ is
--
--      $$\operatorname{child}(v,n)=(v_1,\dots,v_k,\,n+1),$$
--
--      the sequence $v$ extended by the positive integer $n+1$. Thus $n\mapsto\operatorname{child}(v,n)$ enumerates the children of $v$ bijectively by the natural numbers.
--
--   2. **Weakly null sequences.** A sequence $(u_n)_{n\in\mathbb N}$ in a real normed space $X$ is *weakly null* if $f(u_n)\to 0$ as $n\to\infty$ for every continuous linear functional $f\in X^*$.
--
--   These two notions are the combinatorial and the functional-analytic input of the tree obstruction: a family of unit vectors indexed by the tree, whose differences along the children of each vertex have a fixed positive norm and are weakly null, admits no equivalent asymptotically uniformly convex norm.
--
--   **Formalization Note** Vertices are `List ℕ+` and `child v n` is `v ++ [⟨n + 1, _⟩]`. `WeaklyNull` is stated directly against continuous real-linear maps `X →L[ℝ] ℝ` rather than through the weak topology.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts

/-- Natural enumeration of the positive-integer children. -/
def child (v : Vertex) (n : ℕ) : Vertex := v ++ [⟨n + 1, Nat.succ_pos n⟩]

section AbstractObstruction

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Weak convergence to zero, stated directly against continuous real linear functionals. -/
def WeaklyNull (u : ℕ → X) : Prop :=
  ∀ f : X →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 0)

end AbstractObstruction
end IndependentProducts

namespace IndependentProducts
section RadialGrowth
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

end RadialGrowth
end IndependentProducts

namespace IndependentProducts
section TreeObstruction
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

end TreeObstruction
end IndependentProducts

end

end OAI


