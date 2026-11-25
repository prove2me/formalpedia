-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:55.923964+00:00
-- url     : https://prove2.me/theorems/91f68780-d6d7-541b-9deb-8b8aaa13a1d6
-- title:
--   Sub Family Twist St
-- statement:
--   Definitions and structural lemmas for Sub Family Twist St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SubFamilyTwistSt.lean

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
open MvPolynomial
noncomputable section
universe u v w
def SubFamilyTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (Q : LineBundle S x), (∀ I, (F.sub I).FG) →
    ∃ G : SubFamily S x E, G.toSubSystem = F.toSubSystem.twist Q.toSubSystem ∧ ∀ I, (G.sub I).FG
end
end GroundTheory.Heights₂.Heights.Kleiman


