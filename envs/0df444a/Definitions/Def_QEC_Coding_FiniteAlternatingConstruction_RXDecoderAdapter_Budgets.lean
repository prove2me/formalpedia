-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:11:29.684518+00:00
-- url     : https://prove2.me/theorems/ad3c6053-9175-4e71-b30e-c0ddf4594547
-- title:
--   Budgets
-- statement:
--   Definitions and structural lemmas for Budgets, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Budgets.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
end QEC.Coding.BDL26RXDecoderAdapter


