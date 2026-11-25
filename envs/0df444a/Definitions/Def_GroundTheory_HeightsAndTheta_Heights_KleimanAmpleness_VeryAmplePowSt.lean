-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmplePowSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmplePowSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:12.432225+00:00
-- url     : https://prove2.me/theorems/1e4a2e10-927f-40ec-9038-32e0b509fc77
-- title:
--   Very Ample Pow St
-- statement:
--   Definitions and structural lemmas for Very Ample Pow St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmplePowSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
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
universe u w
def VeryAmplePow.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (H : LineBundle S x) (j : ℕ), IsVeryAmple H.toSubSystem → 1 ≤ j →
    IsVeryAmple (H.toSubSystem.pow j)
end
end GroundTheory.Heights₂.Heights.Kleiman


