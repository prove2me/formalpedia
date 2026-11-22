-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelGatherings_GramDetIsUnit
-- name    : Formalism_LocalToGlobal_GroupLattices_LevelGatherings_GramDetIsUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:55.628936+00:00
-- url     : https://prove2.me/theorems/ea09f99d-a0da-4777-a3cf-c5750bbaced8
-- title:
--   Gram Det Is Unit
-- statement:
--   Definitions and structural lemmas for Gram Det Is Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelGatherings/GramDetIsUnit.lean

import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions NumberField Formalism.UG
namespace Formalism.L2.G
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
end Formalism.L2.G


