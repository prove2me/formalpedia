-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffMult
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffMult
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:11.401654+00:00
-- url     : https://prove2.me/theorems/b17c927f-10bf-4a42-8b8e-e3cc582b7255
-- title:
--   Diff Mult
-- statement:
--   Definitions and structural lemmas for Diff Mult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffMult.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_GrpBridge
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
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


