-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_realClass
-- name    : Development_AutomorphicArithmetic_ConductorsKronecker_realClass
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:54:57.879696+00:00
-- url     : https://prove2.me/theorems/edd93337-11e1-416a-8a54-62f42c34a7ca
-- title:
--   real Class
-- statement:
--   Definitions and structural lemmas for real Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/realClass.lean

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_realCond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal


