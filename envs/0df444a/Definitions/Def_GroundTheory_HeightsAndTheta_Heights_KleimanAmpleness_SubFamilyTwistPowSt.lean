-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistPowSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistPowSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:30:49.965215+00:00
-- url     : https://prove2.me/theorems/a1375208-90d9-5aca-b9bd-55602a6db168
-- title:
--   Sub Family Twist Pow St
-- statement:
--   Definitions and structural lemmas for Sub Family Twist Pow St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SubFamilyTwistPowSt.lean

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
def SubFamilyTwistPow.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (Q : SubFamily S x Ω) (a : ℕ),
    ∃ G : SubFamily S x E, G.toSubSystem = F.twist (Q.pow a)
end
end GroundTheory.Heights₂.Heights.Kleiman


