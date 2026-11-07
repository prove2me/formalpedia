-- Prove2me | Definitions.Def_QEC_Results_LocalityBounds_OptimalTradeoff
-- name    : QEC_Results_LocalityBounds_OptimalTradeoff
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T01:08:35.72521+00:00
-- url     : https://prove2.me/theorems/0c36aee6-bbb0-4e21-a6ae-d6d6d6c29fc7
-- title:
--   Optimal Tradeoff
-- statement:
--   Definitions and structural lemmas for Optimal Tradeoff, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/OptimalTradeoff.lean

import Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
open Coding.StabilizerCode.StabilizerParameterData
universe u v
end QEC.Locality


