-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNSandwich
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GNSandwich
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:34.144635+00:00
-- url     : https://prove2.me/theorems/7374c9eb-8b58-4b4a-ba43-fe2cbd780c1f
-- title:
--   GNSandwich
-- statement:
--   Definitions and structural lemmas for GNSandwich, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GNSandwich.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OoConvOf
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
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


