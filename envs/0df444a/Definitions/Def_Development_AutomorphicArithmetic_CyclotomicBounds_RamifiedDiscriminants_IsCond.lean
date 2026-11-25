-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_IsCond
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_IsCond
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:20:55.384596+00:00
-- url     : https://prove2.me/theorems/69ec2939-1924-5411-bbb1-b1cfbecf8b7f
-- title:
--   Is Cond
-- statement:
--   Definitions and structural lemmas for Is Cond, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/IsCond.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace UpperTheory.Ram
open Formalism.L2.Host Formalism.HC Formalism.HC.Der Formalism.FrobeniusOrbits
end UpperTheory.Ram


