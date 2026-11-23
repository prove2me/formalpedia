-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:35.496101+00:00
-- url     : https://prove2.me/theorems/5c518ee2-ec4d-450f-a66c-b73e9bc4c288
-- title:
--   Exists Eq Cexp Quadratic Of Equivalent Factors
-- statement:
--   Definitions and structural lemmas for Exists Eq Cexp Quadratic Of Equivalent Factors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqCexpQuadraticOfEquivalentFactors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
namespace GlobalTheory
section Log
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
end Log
section Factor
variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
end Factor
section Unimodular
variable {L L' : Type*} [AddCommGroup L] [AddCommGroup L']
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V']
  [NormedSpace ℝ V'] [IsScalarTower ℝ ℂ V']
end Unimodular
end GlobalTheory


