-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingIntegral
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingIntegral
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:01:48.841188+00:00
-- url     : https://prove2.me/theorems/a98a6e9e-60fd-5b36-a99c-0f4a312cf97a
-- title:
--   PAmple Ring Integral
-- statement:
--   Definitions and structural lemmas for PAmple Ring Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingIntegral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
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
open MvPolynomial
namespace AmpleRingIntegral
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
end AmpleRingIntegral
end GroundTheory.Heights₂.Heights.Kleiman


