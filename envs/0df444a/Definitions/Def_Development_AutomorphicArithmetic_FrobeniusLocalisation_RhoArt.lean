-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RhoArt
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_RhoArt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:46.956797+00:00
-- url     : https://prove2.me/theorems/9a9d502d-4929-453b-95c3-c953523316c5
-- title:
--   Rho Art
-- statement:
--   Definitions and structural lemmas for Rho Art, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/RhoArt.lean

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


