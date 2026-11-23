-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_VanishingUnits
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_VanishingUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:17.122284+00:00
-- url     : https://prove2.me/theorems/8e078a5e-d81e-48db-b5b5-d5eef160f7d4
-- title:
--   Vanishing Units
-- statement:
--   Definitions and structural lemmas for Vanishing Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/VanishingUnits.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IsLocalRing
section Group
variable {G : Type*} [CommGroup G]
end Group
section LocalField
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
end LocalField
end GroundTheory.ProfCoh


