-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_kronecker
-- name    : Development_AutomorphicArithmetic_ConductorsKronecker_kronecker
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:51:20.981935+00:00
-- url     : https://prove2.me/theorems/a0414246-d27e-432e-b0be-bdcb63350539
-- title:
--   kronecker
-- statement:
--   Definitions and structural lemmas for kronecker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/kronecker.lean

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_RecH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal


