-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:06:33.78283+00:00
-- url     : https://prove2.me/theorems/51bfbb78-203a-4daf-97e1-37b62688a0d5
-- title:
--   Layer Bot
-- statement:
--   Definitions and structural lemmas for Layer Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/LayerBot.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondESpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CardImgOneDvd
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


