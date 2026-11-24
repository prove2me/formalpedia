-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:37.417848+00:00
-- url     : https://prove2.me/theorems/6089e0e7-e835-40ec-912f-e6b8f41bc87f
-- title:
--   Host Ram
-- statement:
--   Definitions and structural lemmas for Host Ram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostRam.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
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
namespace Formalism.HC
open Formalism.FrobeniusOrbits
namespace HostRaw
variable {φ : Frame} (H : HostRaw φ)
variable {H}
end HostRaw
namespace HostAx
variable {φ : Frame} (H : HostAx φ)
end HostAx
end Formalism.HC
end


