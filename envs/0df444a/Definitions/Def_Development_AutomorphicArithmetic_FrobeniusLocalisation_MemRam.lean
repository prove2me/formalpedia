-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:28:20.33883+00:00
-- url     : https://prove2.me/theorems/95cfe6d3-c596-493c-95c9-1fbf76f10c98
-- title:
--   Mem Ram
-- statement:
--   Definitions and structural lemmas for Mem Ram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MemRam.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
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


