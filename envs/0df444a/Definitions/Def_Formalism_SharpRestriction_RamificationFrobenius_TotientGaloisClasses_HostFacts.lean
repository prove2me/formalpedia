-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:47:39.356953+00:00
-- url     : https://prove2.me/theorems/1958d188-7fd7-4121-8e3c-ad932377bece
-- title:
--   Host Facts
-- statement:
--   Definitions and structural lemmas for Host Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
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
theorem q_prime : H.q.Prime := H.hyp.1
theorem d_prime : H.d.Prime := H.hyp.2.1
theorem QS_ne_zero : H.QS ≠ 0 := H.QS_pos.ne'
theorem condN_ne_zero : H.condN ≠ 0 :=
  Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) H.d_prime.ne_zero
instance neZero_condN : NeZero H.condN := ⟨H.condN_ne_zero⟩
end HostRaw
namespace HostAx
variable {φ : Frame} (H : HostAx φ)
end HostAx
end Formalism.HC
end


