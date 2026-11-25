-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:30:50.847407+00:00
-- url     : https://prove2.me/theorems/0c8ecf05-3207-4b3d-9a8d-0a06e90e51a9
-- title:
--   Very Ample ZTwist St
-- statement:
--   Definitions and structural lemmas for Very Ample ZTwist St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleZTwistSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
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
universe u v w
def VeryAmpleZTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ (a : ℕ) (J : Chart h),
      (Submodule.span (chartRing S h J) {z | ∃ q ∈ twistMod S h (a : ℤ) J,
          ∃ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J, z = q • y}).restrictScalars S =
        secsOnZ (F.twist (H.pow a)) H.toSubSystem h J
end
end GroundTheory.Heights₂.Heights.Kleiman


