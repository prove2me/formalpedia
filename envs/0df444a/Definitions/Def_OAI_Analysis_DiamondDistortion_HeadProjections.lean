-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_HeadProjections
-- name    : OAI_Analysis_DiamondDistortion_HeadProjections
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:35:16.63613+00:00
-- url     : https://prove2.me/theorems/c3634419-cf99-46a4-9e59-62e02389e832
-- title:
--   Inclusion order on finite ancestor-closed heads of the countably branching forest
-- statement:
--   For $k\in\mathbb{N}$ let $T_k$ be the rooted, countably branching tree of height $k$: $T_0=\{o\}$, and $T_{k+1}=\{o\}\sqcup(\mathbb{N}\times T_k)$ is a root $o$ with countably many disjoint copies $\{i\}\times T_k$ of $T_k$ below it. The ancestor set $\operatorname{anc}(s)\subseteq T_k$ of a vertex $s$ consists of the vertices on the path from the root to $s$, both included; recursively $\operatorname{anc}(o)=\{o\}$ and $\operatorname{anc}(i,t)=\{o\}\cup\{(i,t'):t'\in\operatorname{anc}(t)\}$. The *forest* is the disjoint union
--   $$
--   \mathcal{F}=\bigsqcup_{h\in\mathbb{N}}T_{h+1}=\{(h,s):\ h\in\mathbb{N},\ s\in T_{h+1}\},
--   $$
--   with one tree of each positive height, and the ancestors of $(h,s)$ are the vertices $(h,t)$ with $t\in\operatorname{anc}(s)$.
--
--   A *finite head* is a finite set $H\subseteq\mathcal{F}$ that is closed under ancestors: whenever $x\in H$, every ancestor of $x$ lies in $H$. The file equips the set of finite heads with the partial order of inclusion,
--   $$
--   H\le K\iff H\subseteq K .
--   $$
--
--   Finite heads ordered by inclusion form a directed set (the union of two finite heads is again a finite head), so they can index nets of coordinate projections onto finite heads in the coordinate spaces built on the forest. The ancestor-closure condition is what is used to compare the norm of the restriction of a vector to a head with the norm of the vector itself.
--
--   **Formalization Note** The type of finite heads is `ForestHead`, the subtype of finite sets of `ForestCoord` (pairs of a height index $h$ and a vertex of `Coord (h+1)`) that are closed under `forestAncestors`. The partial order instance is inherited from the subtype, i.e. it is inclusion of the underlying finite sets; this instance is the only declaration of the definition file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/HeadProjections.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/HeadProjections.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveBounds
import Definitions.Def_OAI_Analysis_DiamondDistortion_SignCube

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace LpCut
variable {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
end LpCut

namespace RecursiveModel
end RecursiveModel

namespace PathModel
open RecursiveModel
end PathModel

namespace CoordinateCompletion.Data
variable {ι : Type*} (A : CoordinateCompletion.Data ι)
end CoordinateCompletion.Data

namespace RecursiveModel
instance : PartialOrder ForestHead := inferInstanceAs (PartialOrder {H : Finset ForestCoord // ∀ i ∈ H,forestAncestors i ⊆ H})
end RecursiveModel

namespace PathModel
open RecursiveModel
end PathModel

end DiamondDistortion

end

end OAI


