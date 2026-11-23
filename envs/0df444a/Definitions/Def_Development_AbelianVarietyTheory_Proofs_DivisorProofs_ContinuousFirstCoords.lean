-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:03.990856+00:00
-- url     : https://prove2.me/theorems/3a8d772d-8f75-4275-8e29-a9b7b5a3c48b
-- title:
--   Continuous First Coords
-- statement:
--   Definitions and structural lemmas for Continuous First Coords, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousFirstCoords.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SphereMeanDrop
open MeasureTheory Set
def gaussProb (n : ℕ) : Measure (EuclideanSpace ℂ (Fin n)) :=
  ProbabilityTheory.cond ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2))) univ
def radProb (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  ProbabilityTheory.cond ((Measure.volumeIoiPow (2 * n - 1)).withDensity
    fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ
def firstCoords {N n : ℕ} (h : N ≤ n) (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun j => WithLp.ofLp x (Fin.castLE h j)
end GlobalTheory.SphereMeanDrop


