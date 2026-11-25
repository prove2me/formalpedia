-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormsEverywhere
-- name    : GroundTheory_GlobalFields_IdeleGroups_LocalNormsEverywhere
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:03:42.775267+00:00
-- url     : https://prove2.me/theorems/657753a7-cbf0-5636-8c32-788909b55d15
-- title:
--   Local Norms Everywhere
-- statement:
--   Definitions and structural lemmas for Local Norms Everywhere, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
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
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
noncomputable section
namespace IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
end IdeleNorm
end
end GroundTheory.Global


