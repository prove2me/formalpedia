-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
-- name    : Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:10:44.390843+00:00
-- url     : https://prove2.me/theorems/bf10299e-5249-4db2-a816-b95006ee7579
-- title:
--   Small Ram
-- statement:
--   Definitions and structural lemmas for Small Ram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/SmallRam.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Ideal
noncomputable section
namespace Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
end Formalism.HC.HostAx
end


