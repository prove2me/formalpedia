-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_GrpBridge
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_GrpBridge
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:43:19.773646+00:00
-- url     : https://prove2.me/theorems/4995fec7-a3c5-47dd-867c-fceb4fd9da06
-- title:
--   Grp Bridge
-- statement:
--   Definitions and structural lemmas for Grp Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/GrpBridge.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_ArtLSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise


