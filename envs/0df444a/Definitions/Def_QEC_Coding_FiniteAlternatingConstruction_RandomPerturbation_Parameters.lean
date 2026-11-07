-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:06.457958+00:00
-- url     : https://prove2.me/theorems/2a618ada-37d3-497b-9b3b-6529b190b09a
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def widthFactor : ℝ := 1 - Real.cos (1 / 6)
noncomputable def perturbationScale (alpha probabilityConstant : ℝ) (D : ℕ) : ℝ :=
  max 1 (max (13 / (2 * alpha + 1)) (4 * probabilityConstant * (D + 1)))
end QEC.Coding.BDL26RandomPerturbation


