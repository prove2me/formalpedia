-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T17:09:12.086731+00:00
-- url     : https://prove2.me/theorems/d7bb51ae-9b03-4cfa-acd1-8bb77b5fd98e
-- title:
--   inert Q
-- statement:
--   Definitions and structural lemmas for inert Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/inertQ.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
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


