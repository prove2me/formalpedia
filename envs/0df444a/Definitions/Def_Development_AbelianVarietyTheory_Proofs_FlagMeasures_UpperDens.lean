-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:26.291236+00:00
-- url     : https://prove2.me/theorems/63631a30-bd3e-41de-b777-099a7cf51f14
-- title:
--   Upper Dens
-- statement:
--   Definitions and structural lemmas for Upper Dens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UpperDens.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace GlobalTheory.HaarDensChart
def upperDens {V : Type} [PseudoMetricSpace V] [MeasurableSpace V] (l ν : Measure V) (x : V) : ℝ≥0∞ :=
  limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0)
end GlobalTheory.HaarDensChart


