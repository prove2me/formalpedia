-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
-- name    : QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:16:50.028205+00:00
-- url     : https://prove2.me/theorems/3a7a6fcc-4450-45a6-b5e6-ced0ddf7a69e
-- title:
--   Directed Distance
-- statement:
--   Definitions and structural lemmas for Directed Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/DirectedDistance.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
set_option autoImplicit false
namespace QEC.Coding.MultiscaleDecoder.DirectedGraph
universe v
variable {V : Type v} [Fintype V] [DecidableEq V]
end QEC.Coding.MultiscaleDecoder.DirectedGraph


