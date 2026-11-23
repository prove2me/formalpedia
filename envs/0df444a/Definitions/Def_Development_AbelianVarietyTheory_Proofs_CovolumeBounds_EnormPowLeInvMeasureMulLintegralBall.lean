-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:32.590094+00:00
-- url     : https://prove2.me/theorems/5b1344ee-0556-4c82-abb4-996a4ce8da61
-- title:
--   Enorm Pow Le Inv Measure Mul Lintegral Ball
-- statement:
--   Definitions and structural lemmas for Enorm Pow Le Inv Measure Mul Lintegral Ball, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
namespace GlobalTheory
section Circle
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
end Circle
section Haar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
end Haar
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
end Volume
section Euclidean
variable {ι : Type*} [Fintype ι]
end Euclidean
end GlobalTheory


