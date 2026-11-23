-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslate
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:02:24.151346+00:00
-- url     : https://prove2.me/theorems/bac0b9df-3e49-4e4b-a2e9-dae2ef532b6f
-- title:
--   Exists Measurable Partition Of Unity Unit Log Translate
-- statement:
--   Definitions and structural lemmas for Exists Measurable Partition Of Unity Unit Log Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMeasurablePartitionOfUnityUnitLogTranslate.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped ContDiff
noncomputable section
namespace GlobalTheory
namespace UnitLogPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I] {φ : I → K →+* ℂ}
def idx (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) : I := (hφ w.embedding).exists.choose
def mean (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : ℝ :=
  (∑ w : InfinitePlace K, y (idx hφ w)) / Fintype.card (InfinitePlace K)
def proj (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : logSpace K :=
  fun w => y (idx hφ w.1) - mean hφ y
end UnitLogPartition
end GlobalTheory


