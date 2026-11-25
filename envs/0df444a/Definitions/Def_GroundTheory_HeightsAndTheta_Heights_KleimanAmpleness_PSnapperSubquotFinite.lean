-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSubquotFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSubquotFinite
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:34.065485+00:00
-- url     : https://prove2.me/theorems/2127d8f4-156c-4f68-aaea-e6774f25a2dc
-- title:
--   PSnapper Subquot Finite
-- statement:
--   Definitions and structural lemmas for PSnapper Subquot Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSubquotFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
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
namespace SnapperSubquotientFinite
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
end SnapperSubquotientFinite
end
end GroundTheory.Heights₂.Heights.Kleiman


