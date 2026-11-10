-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeAsymptotics
-- name    : QEC_Coding_FiniteAlternatingConstruction_QuantitativeAsymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:23:55.397935+00:00
-- url     : https://prove2.me/theorems/e9491d84-57d0-476b-9ce6-ac500521ec2c
-- title:
--   Quantitative Asymptotics
-- statement:
--   Definitions and structural lemmas for Quantitative Asymptotics, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeAsymptotics.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false
namespace QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
def evenGrowthEnvelope (S : OddScale) : Nat := 8 * faceGrowthFactor S ^ 2
end QEC.Coding.BDL26QuantitativeBounds


