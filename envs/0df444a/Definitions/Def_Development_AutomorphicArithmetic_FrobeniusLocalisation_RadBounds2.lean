-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RadBounds2
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_RadBounds2
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T17:07:35.467393+00:00
-- url     : https://prove2.me/theorems/03eeefb0-b545-4ea3-bfb1-109a2082a643
-- title:
--   Rad Bounds2
-- statement:
--   Definitions and structural lemmas for Rad Bounds2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/RadBounds2.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RadBounds
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_NormDiffEK
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RdLower
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


