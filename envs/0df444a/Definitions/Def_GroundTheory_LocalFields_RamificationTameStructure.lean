-- Prove2me | Definitions.Def_GroundTheory_LocalFields_RamificationTameStructure
-- name    : GroundTheory_LocalFields_RamificationTameStructure
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:06:12.188441+00:00
-- url     : https://prove2.me/theorems/95d36724-33b5-4fcf-bca1-b84555b42bba
-- title:
--   Ramification Tame Structure
-- statement:
--   Definitions and structural lemmas for Ramification Tame Structure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationTameStructure.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationTame
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped IntermediateField
namespace GroundTheory.LocalField
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
end GroundTheory.LocalField


