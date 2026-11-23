-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:32.39103+00:00
-- url     : https://prove2.me/theorems/546a70aa-c69d-4b9c-b1aa-0ec55145651f
-- title:
--   Exists Level Structure Of Weil Pairing
-- statement:
--   Definitions and structural lemmas for Exists Level Structure Of Weil Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.LevelOfPairing
section Abstract
variable {G U : Type} [Group G] [CommGroup U] {R : G → G → U → Prop} {M : ℕ}
end Abstract
end GlobalTheory.LevelOfPairing
namespace GlobalTheory
end GlobalTheory


