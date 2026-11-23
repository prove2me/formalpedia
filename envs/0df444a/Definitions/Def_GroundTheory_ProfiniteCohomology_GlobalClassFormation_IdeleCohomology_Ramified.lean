-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_IdeleCohomology_Ramified
-- name    : GroundTheory_ProfiniteCohomology_GlobalClassFormation_IdeleCohomology_Ramified
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:16.748646+00:00
-- url     : https://prove2.me/theorems/258f4599-ed91-4c74-a973-b5963bffc908
-- title:
--   Ramified
-- statement:
--   Definitions and structural lemmas for Ramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/IdeleCohomology/Ramified.lean

import Mathlib
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
open IsDedekindDomain NumberField
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
end GroundTheory.ProfCoh


