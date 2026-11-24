-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:27:46.4678+00:00
-- url     : https://prove2.me/theorems/4b393247-1679-467b-90de-9721ab3d4a62
-- title:
--   Log Rd Sum
-- statement:
--   Definitions and structural lemmas for Log Rd Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/LogRdSum.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
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


