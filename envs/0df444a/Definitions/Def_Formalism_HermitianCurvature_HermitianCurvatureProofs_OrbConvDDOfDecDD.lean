-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:42:35.064858+00:00
-- url     : https://prove2.me/theorems/07a975ce-a5e8-4627-8e90-2e317cbecffc
-- title:
--   Orb Conv DDOf Dec DD
-- statement:
--   Definitions and structural lemmas for Orb Conv DDOf Dec DD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbConvDDOfDecDD.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CkOnZeroOfContOn
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
open scoped InnerProductSpace
namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
end Formalism.FourierDecayAlt.P.S3dx4


