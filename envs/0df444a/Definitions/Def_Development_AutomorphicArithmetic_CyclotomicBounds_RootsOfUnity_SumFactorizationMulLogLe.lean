-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_SumFactorizationMulLogLe
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_SumFactorizationMulLogLe
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:08:00.486496+00:00
-- url     : https://prove2.me/theorems/835f1d78-0a9f-45dd-802a-4fa1a67e1266
-- title:
--   Sum Factorization Mul Log Le
-- statement:
--   Definitions and structural lemmas for Sum Factorization Mul Log Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/SumFactorizationMulLogLe.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TotientLeOfCycPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_NuLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_NuQDUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HC KStar.Tree


