-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:02:43.165403+00:00
-- url     : https://prove2.me/theorems/35759728-104e-4d79-b049-9c7767b456aa
-- title:
--   PIdeal Twist Family
-- statement:
--   Definitions and structural lemmas for PIdeal Twist Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean

import Mathlib
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
namespace IdealTwistFamily
section Forms
variable {R : Type u} [CommRing R] {N : ℕ}
end Forms
section Chart
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
end Chart
end IdealTwistFamily
end
end GroundTheory.Heights₂.Heights.Kleiman


