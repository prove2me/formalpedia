-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
-- name    : GroundTheory_GlobalFields_KummerTheory_LocalIndex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:09.658943+00:00
-- url     : https://prove2.me/theorems/f905fc44-b1b0-4e76-9430-fe78167b19b8
-- title:
--   Local Index
-- statement:
--   Definitions and structural lemmas for Local Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Filtration
end Filtration
section PowerMap
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd
end PowerMap
section Units
variable {n : ℕ}
end Units
section Open
end Open
end GroundTheory.Global


