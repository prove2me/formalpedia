-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable
-- name    : OAI_Analysis_DiamondDistortion_Incomparable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:17:59.238878+00:00
-- url     : https://prove2.me/theorems/2998ffa5-9194-4fc2-b588-f90a1df48ff5
-- title:
--   Incomparable segment families in the segment forest
-- statement:
--   This file singles out the segment families of the segment forest in which vertices taken from different segments are always incomparable.
--
--   **Setting.** The segment forest has vertices $(h,w)$, where $h\ge1$ is an integer and $w$ is a finite word over $\mathbb{N}$ of length at most $h$. A vertex $(h,w)$ is an ancestor of $(h',w')$, written $(h,w)\preceq(h',w')$, if $h=h'$ and $w$ is a prefix of $w'$; this is a partial order in which the ancestors of any vertex form a chain, and each value of $h$ gives one tree component. A *segment* is a finite order interval $[a,b]=\{v:\ a\preceq v\preceq b\}$ with $a\preceq b$. A *segment family* is a finite list $S_1,\dots,S_n$ ($n\ge0$) of pairwise disjoint segments.
--
--   1. **Incomparable families.** A segment family $S_1,\dots,S_n$ is *incomparable* if any two vertices taken from two different segments are incomparable:
--   $$\forall\, i\ne j,\ \ \forall\, u\in S_i,\ \ \forall\, v\in S_j:\qquad u\not\preceq v\quad\text{and}\quad v\not\preceq u.$$
--   2. **The collection of incomparable families.** The incomparable segment families form a nonempty collection: the empty family ($n=0$) is incomparable.
--
--   Incomparability is strictly more restrictive than disjointness; for instance, two disjoint segments on one root-to-leaf branch are comparable. Such families index an incomparable-segment variant of the segment norm, in which the supremum of $\bigl(\sum_i\bigl(\sum_{v\in S_i}u_v\bigr)^2\bigr)^{1/2}$ is taken only over incomparable families instead of all disjoint segment families.
--
--   **Formalization Note** Vertices are `ForestNode`, the ancestor relation is `ForestAncestor` (equal first coordinate and `List.IsPrefix` on the words), and segment families are `forestSegments.Family` (fields `n`, `seg`, `allowed`, `disjoint`). `IncomparableModel.Incomparable F` is stated with `Pairwise` over the indices of `F`, `IncomparableModel.Family` is the corresponding subtype, and its `Nonempty` instance is given by the empty family.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Incomparable.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Incomparable.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace IncomparableModel
open Forest
/-- Every node of one admissible segment is incomparable with every node of
    another. This is strictly more restrictive than disjointness. -/
def Incomparable (F : forestSegments.Family) : Prop :=
  Pairwise (fun i j => ∀ u ∈ F.seg i,∀ v ∈ F.seg j,
    ¬ ForestAncestor u v ∧ ¬ ForestAncestor v u)
def Family := {F : forestSegments.Family // Incomparable F}
instance : Nonempty Family := ⟨⟨{
  n := 0
  seg := Fin.elim0
  allowed := fun i => Fin.elim0 i
  disjoint := by intro i; exact Fin.elim0 i },by intro i; exact Fin.elim0 i⟩⟩
end IncomparableModel

end DiamondDistortion

end

end OAI


