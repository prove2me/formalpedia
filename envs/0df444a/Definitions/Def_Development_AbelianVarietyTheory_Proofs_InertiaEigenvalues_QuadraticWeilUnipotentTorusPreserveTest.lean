-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:49.476803+00:00
-- url     : https://prove2.me/theorems/265d8019-3e2d-42a1-a9c9-b676dbee1263
-- title:
--   Quadratic Weil Unipotent Torus Preserve Test
-- statement:
--   Definitions and structural lemmas for Quadratic Weil Unipotent Torus Preserve Test, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilUnipotentTorusPreserveTest.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.WeilQuad
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
theorem continuous_mulLeft (A : Et F E) (c : A.L) : Continuous fun y : A.L => c * y := by
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  exact IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft F c)
def smulHomeo (A : Et F E) (s : A.Kˣ) : A.L ≃ₜ A.L where
  toFun y := (s : A.K) • y
  invFun y := ((s⁻¹ : A.Kˣ) : A.K) • y
  left_inv y := by simp [smul_smul]
  right_inv y := by simp [smul_smul]
  continuous_toFun := by
    simp only [Algebra.smul_def]; exact continuous_mulLeft A _
  continuous_invFun := by
    simp only [Algebra.smul_def]; exact continuous_mulLeft A _
end GlobalTheory.JR.WeilQuad


