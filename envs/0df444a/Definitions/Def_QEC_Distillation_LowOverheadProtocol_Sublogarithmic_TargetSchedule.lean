-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
-- name    : QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:36:38.768662+00:00
-- url     : https://prove2.me/theorems/ab3dd479-577e-4092-b431-140c46f19681
-- title:
--   Target Schedule
-- statement:
--   Definitions and structural lemmas for Target Schedule, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
def doublePowerTarget (q : ℝ) (d z : Nat) : ℝ := q ^ (d ^ z)
noncomputable def concatenationExponent (n k d : Nat) : ℝ :=
  Real.log ((n : ℝ) / k) / Real.log d
noncomputable def rawSuccessAdjustmentCoefficient
    (q sigma : ℝ) (n k d : Nat) : ℝ :=
  (1 / sigma) /
    Real.rpow (Real.log (1 / q)) (concatenationExponent n k d)
def selectedDoublePowerTarget (q : ℝ) (A D j z : Nat) : ℝ :=
  doublePowerTarget q (parameterDistance A D j) z
noncomputable def selectedSuccessAdjustmentCoefficient (q sigma : ℝ)
    (A D j : Nat) : ℝ :=
  rawSuccessAdjustmentCoefficient q sigma (parameterLength A D j)
    (parameterDimension A D j) (parameterDistance A D j)
end QEC.Distillation.HH18.HH18SublogarithmicEntropy


