-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobHOrder
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobHOrder
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:44:17.950969+00:00
-- url     : https://prove2.me/theorems/679ec317-bf5b-49d9-a8b6-7d1ef06ae421
-- title:
--   Frob HOrder
-- statement:
--   Definitions and structural lemmas for Frob HOrder, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/FrobHOrder.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobGSpec
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


