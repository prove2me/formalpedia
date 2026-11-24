-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNonvanishingFromL2
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNonvanishingFromL2
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T20:39:28.266959+00:00
-- url     : https://prove2.me/theorems/3c52d119-a66a-47b9-b959-b846d76aed49
-- title:
--   Bessel Nonvanishing From L2
-- statement:
--   Definitions and structural lemmas for Bessel Nonvanishing From L2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselNonvanishingFromL2.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReproducingFormulaReduction
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
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
open Formalism.FourierDecayAlt.ThreeDimData
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity


