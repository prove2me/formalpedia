-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:05.261368+00:00
-- url     : https://prove2.me/theorems/bfda0e0f-4805-42f4-877f-3f7be910d73d
-- title:
--   Statements Ideal Twist
-- statement:
--   Definitions and structural lemmas for Statements Ideal Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsIdealTwist.lean

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
universe u w
def IdealTwistFamily.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (J' : Ideal (Poly S N)),
    (∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') →
    ∃ F : SubFamily S x Ω, F.toSubSystem = Q.twist (idealSys x J') ∧ ∀ I, (F.sub I).FG
end
end GroundTheory.Heights₂.Heights.Kleiman


