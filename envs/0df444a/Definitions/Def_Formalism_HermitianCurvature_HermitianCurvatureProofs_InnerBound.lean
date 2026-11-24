-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:17.212799+00:00
-- url     : https://prove2.me/theorems/54310381-17e7-4678-b625-f9a23de1cada
-- title:
--   Inner Bound
-- statement:
--   Definitions and structural lemmas for Inner Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InnerBound.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNMulRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
end Formalism.FourierDecayAlt.P.S3dx4


