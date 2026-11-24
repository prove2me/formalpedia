-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingIntegralSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingIntegralSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:38.730647+00:00
-- url     : https://prove2.me/theorems/6ceaf16a-4ecf-4555-b1fa-cc9857cf52c7
-- title:
--   Ample Ring Integral St
-- statement:
--   Definitions and structural lemmas for Ample Ring Integral St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AmpleRingIntegralSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
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
def AmpleRingIntegral.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (H : LineBundle S x) (D : AmpleData S x H) (j : Fin (D.r + 1)), D.h j ≠ 0 →
      ∀ f ∈ ampleRing H.toSubSystem D.m (D.h j), IsIntegral (ampleBase (S := S) D.h j) f
end GroundTheory.Heights₂.Heights.Kleiman


