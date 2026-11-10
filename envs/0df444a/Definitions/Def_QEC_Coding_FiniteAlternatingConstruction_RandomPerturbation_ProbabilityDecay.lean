-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:02:10.495681+00:00
-- url     : https://prove2.me/theorems/ff52fc93-4aeb-4c6c-9e92-6c8befa8f352
-- title:
--   Probability Decay
-- statement:
--   Definitions and structural lemmas for Probability Decay, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ProbabilityDecay.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventProbability
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
noncomputable def probabilityCoefficient (a : ℕ) (c : ℝ) : ℝ :=
  ((2*(a+2)+1 : ℕ)^3 : ℝ)*(125*18/((a : ℝ)*(1-c)))^4
end QEC.Coding.BDL26RandomPerturbation


