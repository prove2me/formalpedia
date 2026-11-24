-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RdLower
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_RdLower
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:55.6208+00:00
-- url     : https://prove2.me/theorems/c24fbcac-7256-442f-8489-e12a6dcee232
-- title:
--   Rd Lower
-- statement:
--   Definitions and structural lemmas for Rd Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/RdLower.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise


