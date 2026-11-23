-- Prove2me | Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
-- name    : GroundTheory_LocalFields_HerbrandCyclic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:04.840204+00:00
-- url     : https://prove2.me/theorems/eb6e1180-010b-4206-9fbe-5a3949f9f224
-- title:
--   Herbrand Cyclic
-- statement:
--   Definitions and structural lemmas for Herbrand Cyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
section Injective
variable {N : Type*} [CommGroup N] [MulDistribMulAction G N]
end Injective
end GroundTheory.LocalField


