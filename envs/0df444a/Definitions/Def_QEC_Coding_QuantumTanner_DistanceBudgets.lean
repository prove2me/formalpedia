-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
-- name    : QEC_Coding_QuantumTanner_DistanceBudgets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:40:32.656938+00:00
-- url     : https://prove2.me/theorems/0a0023d3-e0b2-47d6-afb8-27290512f1a3
-- title:
--   Distance Budgets
-- statement:
--   Definitions and structural lemmas for Distance Budgets, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/DistanceBudgets.lean

import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Filter
def distanceNormalCutoff (epsilon : ℝ) (Delta : Nat) : Nat :=
  Nat.ceil ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon))
def distanceLineError (delta epsilon : ℝ) (Delta : Nat) : Nat :=
  (distanceNormalCutoff epsilon Delta - 1) / Nat.ceil (delta * Delta)
end QEC.Coding.QuantumTanner


