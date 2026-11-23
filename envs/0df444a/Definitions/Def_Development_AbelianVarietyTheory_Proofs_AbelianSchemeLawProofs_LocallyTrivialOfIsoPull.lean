-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocallyTrivialOfIsoPull
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocallyTrivialOfIsoPull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:42.717621+00:00
-- url     : https://prove2.me/theorems/42e1b0c7-f4e5-48d4-8763-225182c48a66
-- title:
--   Locally Trivial Of Iso Pull
-- statement:
--   Definitions and structural lemmas for Locally Trivial Of Iso Pull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocallyTrivialOfIsoPull.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_RigidityTranslation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CubeLawCompare
section General
variable {Y T : Scheme.{0}}
def IsGenOn (M : LB Y) (W : Y.Opens) (d : ∀ j, Γ(Y, W ⊓ M.U j)ˣ) : Prop :=
  ∀ j j' (y : Y), y ∈ W → y ∈ M.U j → y ∈ M.U j' →
    gm (𝟙 Y) y (W ⊓ M.U j) (d j) =
      gm (𝟙 Y) y (M.U j ⊓ M.U j') (M.g j j') * gm (𝟙 Y) y (W ⊓ M.U j') (d j')
end General
end GlobalTheory.CubeLawCompare


