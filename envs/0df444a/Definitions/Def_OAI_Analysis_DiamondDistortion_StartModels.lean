-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
-- name    : OAI_Analysis_DiamondDistortion_StartModels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:11:48.935865+00:00
-- url     : https://prove2.me/theorems/06b50956-e2ff-48d8-814a-cce11b10f908
-- title:
--   Bundled real normed spaces for recursion on the tree height
-- statement:
--   This file introduces a small bundling device for normed spaces.
--
--   A *real normed bundle* is a pair consisting of a type $X$ together with a structure of real normed vector space on $X$: a norm $\|\cdot\|$ making $X$ a normed additive commutative group, compatible with scalar multiplication by $\mathbb{R}$ in the sense that $\|tx\|\le|t|\,\|x\|$ for $t\in\mathbb{R}$, $x\in X$. Completeness is not required. Every bundle can be used directly as the type $X$, which then carries the bundled normed-space structure.
--
--   The point of the bundle is to allow families of normed spaces $X_0,X_1,X_2,\dots$ to be defined by recursion on a natural-number parameter (here, the height of a tree), where $X_{h+1}$ is built from $X_h$: the recursion must produce a single kind of object at each step, so each space is packaged together with its norm.
--
--   **Formalization Note** `StartModel.RealNormed` has fields `carrier : Type`, `group : NormedAddCommGroup carrier` and `space : NormedSpace ℝ carrier`, the latter two registered as instances; a `CoeSort` instance lets a bundle be used as a type. The carrier lives in the lowest universe `Type`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/StartModels.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/StartModels.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace StartModel

section
open RecursiveModel PathModel
/-- A local bundle used only to recurse over the finite tree height. -/
structure RealNormed where
  carrier : Type
  [group : NormedAddCommGroup carrier]
  [space : NormedSpace ℝ carrier]
attribute [instance] RealNormed.group RealNormed.space
instance : CoeSort RealNormed Type := ⟨RealNormed.carrier⟩

end

-- [generator] trimmed: open RecursiveModel PathApplications
open RecursiveModel

end StartModel

namespace PathModel
-- [generator] dropped: open PathApplications

end PathModel

end DiamondDistortion

end

end OAI


