-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
-- name    : GroundTheory_GlobalFields_Artin_InflationTower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:52.238955+00:00
-- url     : https://prove2.me/theorems/fb69817c-444c-4a2c-bbce-727f4dfc7eea
-- title:
--   Inflation Tower
-- statement:
--   Definitions and structural lemmas for Inflation Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
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
open IsDedekindDomain NumberField
open scoped Pointwise
namespace GroundTheory.Global
section Average
variable {G H : Type*} [Group G] [Group H]
end Average
variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [IsGalois K F] [IsGalois K L]
end GroundTheory.Global


