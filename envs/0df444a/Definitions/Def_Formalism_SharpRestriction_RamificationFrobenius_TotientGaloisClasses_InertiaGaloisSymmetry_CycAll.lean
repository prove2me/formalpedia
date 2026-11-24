-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:34.020439+00:00
-- url     : https://prove2.me/theorems/691b3b87-ac02-4a92-a392-1f615f9f8f09
-- title:
--   Cyc All
-- statement:
--   Definitions and structural lemmas for Cyc All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycAll.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
end Formalism.HC.Der
end


