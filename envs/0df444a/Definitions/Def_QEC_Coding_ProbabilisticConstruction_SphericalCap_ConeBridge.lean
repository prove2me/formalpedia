-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
-- name    : QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:52:38.654397+00:00
-- url     : https://prove2.me/theorems/acd93f07-682c-440f-800e-532c97b6c841
-- title:
--   Cone Bridge
-- statement:
--   Definitions and structural lemmas for Cone Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeBridge.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
def solidCapCone (u : Sphere) (c : ℝ) : Set Space :=
  {x | ‖x‖ ≤ 1 ∧ c * ‖x‖ ≤ inner ℝ (u : Space) x}
end QEC.Coding.ProbabilisticConstruction.SphericalCap


