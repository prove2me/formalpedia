-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralLogNormLeHalfLogIntegralSq
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralLogNormLeHalfLogIntegralSq
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:12:06.532931+00:00
-- url     : https://prove2.me/theorems/2aaa5cc8-d5b8-40ca-a0e2-7695ec765ef7
-- title:
--   Integral Log Norm Le Half Log Integral Sq
-- statement:
--   Definitions and structural lemmas for Integral Log Norm Le Half Log Integral Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralLogNormLeHalfLogIntegralSq.lean

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
open MeasureTheory Metric Set Filter Real
open scoped ENNReal Topology Pointwise
namespace GlobalTheory
section Rotation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
noncomputable def sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨circleMap 0 1 θ • (x : E), by simp [norm_smul]⟩
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
end Rotation
section Torus
variable {ι : Type*} [Fintype ι]
end Torus
section Concavity
variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
end Concavity
end GlobalTheory


