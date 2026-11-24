-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:35.712891+00:00
-- url     : https://prove2.me/theorems/1425921a-3194-47bb-b0ed-1e334c33a509
-- title:
--   Fs Log Reg Basic
-- statement:
--   Definitions and structural lemmas for Fs Log Reg Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section
namespace FubiniStudyLogRegularization
variable {n : ℕ}
def sqDual (h : HermNorm n) (y : Fin n → ℂ) : ℝ := ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2
def regMat (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) : Matrix (Fin (n + 1)) (Fin n) ℂ :=
  Matrix.of (Fin.cons u fun i => ((√ε : ℝ) : ℂ) • (h.matᵀ)⁻¹ i)
end FubiniStudyLogRegularization
end
end GroundTheory.Heights₂.Heights


