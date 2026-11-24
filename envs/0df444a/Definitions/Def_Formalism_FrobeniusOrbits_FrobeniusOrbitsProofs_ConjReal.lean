-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
-- name    : Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:32:48.306993+00:00
-- url     : https://prove2.me/theorems/6ad7c6ee-3793-4871-b288-464437925f67
-- title:
--   Conj Real
-- statement:
--   Definitions and structural lemmas for Conj Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ConjReal.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_JumpSets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace ConjReal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end ConjReal
open ConjReal
end Formalism.FrobeniusOrbits


