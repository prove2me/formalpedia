-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:24:08.057207+00:00
-- url     : https://prove2.me/theorems/80b43ad7-4fa7-4d9e-a3e3-a206a014ef9f
-- title:
--   PInter Num Point
-- statement:
--   Definitions and structural lemmas for PInter Num Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PInterNumPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumPointSt
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
open MvPolynomial Filter
noncomputable section
universe u w
section InterNumPointLemmas
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
end InterNumPointLemmas
end
end GroundTheory.Heights₂.Heights.Kleiman


