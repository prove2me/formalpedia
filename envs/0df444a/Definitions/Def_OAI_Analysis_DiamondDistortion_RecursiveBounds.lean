-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveBounds
-- name    : OAI_Analysis_DiamondDistortion_RecursiveBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:28:13.051867+00:00
-- url     : https://prove2.me/theorems/9603a5f8-c56d-4b24-b98b-4e78647ddaf9
-- title:
--   The tree functional $\nu_h=P_h+Q_h$ on $\ell_p$ of a countably branching tree
-- statement:
--   Fix an exponent $p$ with $1\le p<\infty$. For $h\in\mathbb{N}$ let $T_h$ be the rooted, countably branching tree of height $h$: $T_0=\{o\}$ is a single root, and $T_{h+1}=\{o\}\sqcup(\mathbb{N}\times T_h)$ consists of a root $o$ below which hang countably many disjoint copies $\{i\}\times T_h$ $(i\in\mathbb{N})$ of $T_h$. Let $\ell_p(T_h)$ be the space of $p$-summable real functions on $T_h$, and for $v\in\ell_p(T_{h+1})$ and $i\in\mathbb{N}$ let $v_i\in\ell_p(T_h)$, $v_i(s)=v(i,s)$, be the $i$-th child of $v$. The least upper values $(P_h,Q_h):\ell_p(T_h)\to[0,\infty)^2$ are defined recursively by $P_0(v)=\max(v(o),0)$, $Q_0(v)=\max(-v(o),0)$ and
--   $$
--   P_{h+1}(v)=\max\big(a_v,\ v(o)+b_v\big),\qquad Q_{h+1}(v)=\max\big(a_v-v(o),\ b_v\big),
--   $$
--   where $a_v=\|(P_h(v_i))_{i\in\mathbb{N}}\|_{\ell_p}$ and $b_v=\|(Q_h(v_i))_{i\in\mathbb{N}}\|_{\ell_p}$.
--
--   1. **The functional $\nu_h$.** For $v\in\ell_p(T_h)$,
--   $$
--   \nu_h(v)=P_h(v)+Q_h(v).
--   $$
--   The file records $\nu_h(0)=0$.
--
--   In the surrounding development $\nu_h$ is shown to be a seminorm on $\ell_p(T_h)$ that is equivalent to the $\ell_p$ norm, with $\|v\|_p\le(h+1)\,\nu_h(v)$ and $\nu_h(v)\le2\cdot3^h\,\|v\|_p$. It is the full-space counterpart of the recursive norm that the same recursion defines on finitely supported arrays, and it is one of the recursive tree norms used in the diamond-distortion argument.
--
--   **Formalization Note** `fullNu p hp h v` is the sum of the two components of `fullUpper p hp h v`, where the hypothesis `hp : 0 < p.toReal` excludes $p=\infty$; `fullNu_zero` is the simp lemma $\nu_h(0)=0$. The seminorm properties and the two comparison inequalities are separate lemmas that are not part of this definition file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/RecursiveBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/RecursiveBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
import Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable
import Definitions.Def_OAI_Analysis_DiamondDistortion_ModelMaps
import Definitions.Def_OAI_Analysis_DiamondDistortion_EquivalentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_UpperFunction

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace RecursiveModel

section
variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
def fullNu (h : ℕ) (v : Full p h) : ℝ := (fullUpper p hp h v).1+(fullUpper p hp h v).2
@[simp] lemma fullNu_zero (h : ℕ) : fullNu p hp h 0=0 := by simp [fullNu]
end

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
end RecursiveModel

namespace Midpoint
namespace Heads
variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end Heads

end Midpoint

namespace RecursiveModel
-- [generator] dropped: open RecursiveApplications
end RecursiveModel

end DiamondDistortion

end

end OAI


