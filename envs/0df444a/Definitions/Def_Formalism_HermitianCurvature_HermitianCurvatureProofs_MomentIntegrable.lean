-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MomentIntegrable
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MomentIntegrable
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:10:20.436372+00:00
-- url     : https://prove2.me/theorems/3d3227ed-7908-4e31-862e-e2d2430e7dce
-- title:
--   Moment Integrable
-- statement:
--   Definitions and structural lemmas for Moment Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MomentIntegrable.lean

import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Module
open scoped FourierTransform
noncomputable section
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]
end Formalism.FourierDecayAlt.P5.HerC.Fou


