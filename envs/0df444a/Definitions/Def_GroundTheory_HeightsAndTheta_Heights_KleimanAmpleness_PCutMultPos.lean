-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutMultPos
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutMultPos
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:16:51.986313+00:00
-- url     : https://prove2.me/theorems/4757541f-ef8f-4e9e-8b44-94b4de6b968f
-- title:
--   PCut Mult Pos
-- statement:
--   Definitions and structural lemmas for PCut Mult Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutMultPos.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutMultPosSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
open IsLocalRing
def locQuotEquiv {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] (J : Ideal R) :
    (Localization.AtPrime q ⧸ J.localized' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q))) ≃ₗ[Localization.AtPrime q]
      LocalizedModule q.primeCompl (R ⧸ J) :=
  have := IsLocalization.linearMap_compatibleSMul q.primeCompl
  (IsLocalizedModule.linearEquiv q.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q)))
    (LocalizedModule.mkLinearMap _ _)).restrictScalars _
end
end GroundTheory.Heights₂.Heights.Kleiman


