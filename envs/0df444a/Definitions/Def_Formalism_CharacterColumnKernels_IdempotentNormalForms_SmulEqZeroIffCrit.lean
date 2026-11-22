-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SmulEqZeroIffCrit
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_SmulEqZeroIffCrit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:09.188417+00:00
-- url     : https://prove2.me/theorems/15a8fffb-456c-407e-95b3-cc0490af57f2
-- title:
--   Smul Eq Zero Iff Crit
-- statement:
--   Definitions and structural lemmas for Smul Eq Zero Iff Crit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SmulEqZeroIffCrit.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatCompMultSimple
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
noncomputable section
namespace Formalism.NG
namespace IdempotentCriticalLength
variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]
def Crit (O : Type*) [CommRing O] [IsLocalRing O] [Algebra O Λ] (ε x : Λ) : Prop :=
  ∀ y : Λ, ∀ c : O, ε * (y * x) * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ →
    c ∈ IsLocalRing.maximalIdeal O
end IdempotentCriticalLength
namespace IdempotentCriticalLengthFinite
variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]
end IdempotentCriticalLengthFinite
end Formalism.NG


