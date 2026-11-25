-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubFamilyTwistX
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubFamilyTwistX
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:45.300554+00:00
-- url     : https://prove2.me/theorems/93d830de-7967-41f2-9ead-2abdc8c51664
-- title:
--   PSub Family Twist X
-- statement:
--   Definitions and structural lemmas for PSub Family Twist X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubFamilyTwistX.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubFamilyTwistPow
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
section
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
end
end
end GroundTheory.Heights₂.Heights.Kleiman


