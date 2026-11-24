-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:13:56.154969+00:00
-- url     : https://prove2.me/theorems/bffb6ab1-deeb-4efa-a314-172de170adc9
-- title:
--   Chart Integral Local
-- statement:
--   Definitions and structural lemmas for Chart Integral Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChartIntegralLocal.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.ChartIntegralLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
end Formalism.FourierDecayAlt.P.ChartIntegralLocal


