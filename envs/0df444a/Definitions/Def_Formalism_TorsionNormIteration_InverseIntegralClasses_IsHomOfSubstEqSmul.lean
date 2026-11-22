-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:19.561742+00:00
-- url     : https://prove2.me/theorems/3108c5f4-a0d1-4b2f-bea2-32adac50e1a9
-- title:
--   Is Hom Of Subst Eq Smul
-- statement:
--   Definitions and structural lemmas for Is Hom Of Subst Eq Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Formalism.LT.PadicP
open Formalism.G
def unitBallEquiv (p : ℕ) [Fact p.Prime] : unitBall ℚ_[p] ≃+* ℤ_[p] where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
section LtLog
variable {p : ℕ} [hp : Fact p.Prime]
end LtLog
end Formalism.LT.PadicP
namespace Formalism.LT
end Formalism.LT


