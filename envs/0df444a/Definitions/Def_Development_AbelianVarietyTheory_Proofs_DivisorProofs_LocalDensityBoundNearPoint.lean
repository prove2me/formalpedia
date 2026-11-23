-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:20.316264+00:00
-- url     : https://prove2.me/theorems/554c32da-fc3d-4dee-9999-51c1d666a0b3
-- title:
--   Local Density Bound Near Point
-- statement:
--   Definitions and structural lemmas for Local Density Bound Near Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalDensityBoundNearPoint.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
namespace GlobalTheory.LineCos
def splitLin (d : ℕ) : V (d + 1) ≃ₗ[ℝ] (Fin d → ℂ) × ℂ where
  toFun z := (base z, fib z)
  invFun p := WithLp.toLp 2 (Fin.snoc p.1 p.2 : Fin (d + 1) → ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [fib]
    · simp [base]
  right_inv p := by
    ext i
    · simp [base]
    · simp [fib]
def fsDensity (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  G.det.re / (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2)
end GlobalTheory.LineCos


