-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_NuQDUnit
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_NuQDUnit
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:30.875503+00:00
-- url     : https://prove2.me/theorems/aab02d65-8cee-44f2-ba88-235d4ca2a598
-- title:
--   Nu QDUnit
-- statement:
--   Definitions and structural lemmas for Nu QDUnit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/NuQDUnit.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TotientLeOfCycPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_HostApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HC KStar.Tree


