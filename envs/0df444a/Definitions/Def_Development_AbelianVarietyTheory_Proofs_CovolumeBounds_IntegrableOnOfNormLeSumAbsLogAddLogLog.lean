-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableOnOfNormLeSumAbsLogAddLogLog
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableOnOfNormLeSumAbsLogAddLogLog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:35.647797+00:00
-- url     : https://prove2.me/theorems/319e515c-796d-4b12-b062-cf2fdd2b85f4
-- title:
--   Integrable On Of Norm Le Sum Abs Log Add Log Log
-- statement:
--   Definitions and structural lemmas for Integrable On Of Norm Le Sum Abs Log Add Log Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableOnOfNormLeSumAbsLogAddLogLog.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real
namespace GlobalTheory
section Holomorphic
noncomputable def logGap (M : ℝ) (y : ℂ) : ℝ≥0∞ :=
  if y = 0 then ∞ else ENNReal.ofReal (Real.log M - Real.log ‖y‖)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
end Holomorphic
section Coordinates
open Bornology
variable {ι : Type*} [Fintype ι]
variable {F : Type*} [NormedAddCommGroup F]
end Coordinates
end GlobalTheory


