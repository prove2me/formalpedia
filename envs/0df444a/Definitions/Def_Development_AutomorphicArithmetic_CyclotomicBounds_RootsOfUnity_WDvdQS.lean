-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_WDvdQS
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_WDvdQS
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:32.271924+00:00
-- url     : https://prove2.me/theorems/a1e18e6a-e167-4bb8-b41e-77007ec7689f
-- title:
--   WDvd QS
-- statement:
--   Definitions and structural lemmas for WDvd QS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/WDvdQS.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TotientLeOfCycPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HC KStar.Tree


