-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_HostCls
-- name    : Formalism_LocalRingCardinality_HostCls
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:11:16.859775+00:00
-- url     : https://prove2.me/theorems/f1715db8-9883-4e56-9db4-74b41fdfcd72
-- title:
--   Host Cls
-- statement:
--   Definitions and structural lemmas for Host Cls, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
namespace Formalism.BasicNotions
section cls
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
variable {H}
end cls
namespace Ranks
variable (R : Ranks)
end Ranks
namespace Host
variable {R : Ranks} (H : Host R)
end Host
end Formalism.BasicNotions


