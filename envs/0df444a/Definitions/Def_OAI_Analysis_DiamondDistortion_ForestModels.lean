-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
-- name    : OAI_Analysis_DiamondDistortion_ForestModels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:02:54.705703+00:00
-- url     : https://prove2.me/theorems/b9bd3449-3e1f-4622-95ee-c90f7ab001ce
-- title:
--   Component index and component-restricted coefficient arrays on the forest of countably branching trees
-- statement:
--   Let $\mathcal F$ be the forest whose vertices are the pairs $(h,w)$ with $h\ge1$ an integer and $w$ a finite word over $\mathbb{N}$ of length at most $h$, ordered by $(h,w)\preceq(h',w')$ if and only if $h=h'$ and $w$ is a prefix of $w'$. Thus $\mathcal F$ is the disjoint union, over $h\ge1$, of the rooted tree of height $h$ in which every vertex of depth less than $h$ has countably many children (the root being the empty word). The segments of $\mathcal F$ are its finite order intervals $[a,b]=\{v:\ a\preceq v\preceq b\}$ with $a\preceq b$. On finitely supported $u:\mathcal F\to\mathbb{R}$ the segment norm is
--
--   $$
--   \|u\|=\sup\Big(\sum_{i=1}^n\Big(\sum_{v\in S_i}u(v)\Big)^2\Big)^{1/2},
--   $$
--
--   the supremum running over all finite families $S_1,\dots,S_n$ of pairwise disjoint segments; $J_{\mathcal F}$ is the completion, $J_{\mathcal F}^*$ its full continuous dual, and $e_v\in J_{\mathcal F}$ the image of the indicator of $\{v\}$. The file defines:
--
--   1. **Component.** $\mathrm{comp}(h,w)=h$, the index of the tree containing the vertex $(h,w)$.
--
--   2. **Restricted coefficient array.** For a finite set $C\subseteq\mathbb{N}$ and $x\in J_{\mathcal F}^*$, the function $x_C:\mathcal F\to\mathbb{R}$ given by
--   $$
--   x_C(v)=\begin{cases}x(e_v),&\mathrm{comp}(v)\in C,\\ 0,&\text{otherwise.}\end{cases}
--   $$
--
--   Every segment lies inside a single component, and a segment in component $h$ is a chain with at most $h+1$ vertices. In the surrounding development, cutting a dual functional down to finitely many components through $x_C$ produces coefficient arrays whose finite square sums are bounded in terms of $\|x\|$ and $\max C$; this is a step in approximating arbitrary elements of the full dual $J_{\mathcal F}^*$ by functionals living on finitely many components.
--
--   **Formalization Note** The vertex type is `ForestNode`, a subtype of pairs of a natural number and a list of natural numbers; the segment system is `forestSegments`, and $J_{\mathcal F}^*$ is `forestSegments.Dual`, which is also the space `ForestDual`. The definitions are `Forest.component` and `Forest.coefficients`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/ForestModels.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/ForestModels.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Forest

def component (v : ForestNode) : ℕ := v.val.1

def coefficients (C : Finset ℕ) (x : forestSegments.Dual) (v : ForestNode) : ℝ :=
  if component v ∈ C then x (forestSegments.unitVector v) else 0

end Forest

end DiamondDistortion

end

end OAI


