-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
-- name    : Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:53.562794+00:00
-- url     : https://prove2.me/theorems/8afaf31c-5ced-5c5b-8a3e-23c84aa34b64
-- title:
--   Exists Line Bundle Twist Mul Of
-- statement:
--   Definitions and structural lemmas for Exists Line Bundle Twist Mul Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/ExistsLineBundleTwistMulOf.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PositivityTheory.HtPt.KtwS
open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial
noncomputable section
universe u v w
section Helpers
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
end Helpers
section OnW
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
end OnW
end
end PositivityTheory.HtPt.KtwS


