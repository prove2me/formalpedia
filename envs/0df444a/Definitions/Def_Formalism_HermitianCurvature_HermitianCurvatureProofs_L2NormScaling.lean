-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:10:23.59488+00:00
-- url     : https://prove2.me/theorems/09114fb3-f2e3-43ca-a485-2e79bb1e22cc
-- title:
--   L2 Norm Scaling
-- statement:
--   Definitions and structural lemmas for L2 Norm Scaling, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L2NormScaling.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
namespace Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
section Alg
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
end Alg
end Formalism.FourierDecayAlt.P.DDSmoothness


