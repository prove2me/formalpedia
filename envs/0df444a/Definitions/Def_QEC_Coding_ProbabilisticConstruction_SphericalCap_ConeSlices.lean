-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
-- name    : QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:48:59.752484+00:00
-- url     : https://prove2.me/theorems/6e46d9ac-f0c1-4c85-b265-90f70f6a66f4
-- title:
--   Cone Slices
-- statement:
--   Definitions and structural lemmas for Cone Slices, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal
noncomputable def coneSlopeSq (c : ℝ) : ℝ := (1 - c ^ 2) / c ^ 2
def axialCone (c : ℝ) : Set Ambient :=
  {x | ‖x‖ ≤ 1 ∧ c * ‖x‖ ≤ x 0}
end QEC.Coding.ProbabilisticConstruction.SphericalCap


