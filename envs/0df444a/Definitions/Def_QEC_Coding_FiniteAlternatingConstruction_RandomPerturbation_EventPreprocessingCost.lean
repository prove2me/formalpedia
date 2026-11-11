-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPreprocessingCost
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPreprocessingCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T22:47:45.566853+00:00
-- url     : https://prove2.me/theorems/d2c4be20-69c6-4161-87c7-079e95e4ad91
-- title:
--   Event Preprocessing Cost
-- statement:
--   Definitions and structural lemmas for Event Preprocessing Cost, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventPreprocessingCost.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
def rawUniverseBudget (n : ℕ) : ℕ :=
  13*n^4+n^3+n^2+n+n^4*(100000*(n+1)^2+2)
def eventUniverseBudget (n : ℕ) : ℕ :=
  rawUniverseBudget n+(n^4+1)^2*(24*(n+1)+330)
end QEC.Coding.BDL26RandomPerturbation


