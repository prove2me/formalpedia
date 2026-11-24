-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CkOnZeroOfContOn
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CkOnZeroOfContOn
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:22.438796+00:00
-- url     : https://prove2.me/theorems/5ecf4a63-7012-4c44-a17b-3ac9783df521
-- title:
--   Ck On Zero Of Cont On
-- statement:
--   Definitions and structural lemmas for Ck On Zero Of Cont On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CkOnZeroOfContOn.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
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


