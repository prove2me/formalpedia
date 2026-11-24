-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_ImgOneGcd
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_ImgOneGcd
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:57.909149+00:00
-- url     : https://prove2.me/theorems/1cf1ea75-5768-4be4-ad94-69828ebb17ff
-- title:
--   Img One Gcd
-- statement:
--   Definitions and structural lemmas for Img One Gcd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/ImgOneGcd.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
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


