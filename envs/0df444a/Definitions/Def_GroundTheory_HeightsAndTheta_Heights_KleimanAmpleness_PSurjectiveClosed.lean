-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:12:00.911704+00:00
-- url     : https://prove2.me/theorems/d1ed4839-6620-5a33-9b94-b3351ded8e4b
-- title:
--   PSurjective Closed
-- statement:
--   Definitions and structural lemmas for PSurjective Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
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
namespace SurjectiveClosed
section Signs
variable {n : ℕ}
variable {U : Finset (Fin n)} {A : Type*} [AddCommGroup A]
end Signs
section Twists
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
end Twists
end SurjectiveClosed
end
end GroundTheory.Heights₂.Heights.Kleiman


