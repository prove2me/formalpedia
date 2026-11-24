-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobGSpec
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobGSpec
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:14.139164+00:00
-- url     : https://prove2.me/theorems/a54f340f-e04f-49ca-8da8-e2b4b7f894b4
-- title:
--   Frob GSpec
-- statement:
--   Definitions and structural lemmas for Frob GSpec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/FrobGSpec.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise


