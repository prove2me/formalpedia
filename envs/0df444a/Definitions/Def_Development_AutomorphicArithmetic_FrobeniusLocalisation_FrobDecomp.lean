-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobDecomp
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobDecomp
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:36.903402+00:00
-- url     : https://prove2.me/theorems/2c2445fb-9033-42ce-97b7-54ba073a15df
-- title:
--   Frob Decomp
-- statement:
--   Definitions and structural lemmas for Frob Decomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/FrobDecomp.lean

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


