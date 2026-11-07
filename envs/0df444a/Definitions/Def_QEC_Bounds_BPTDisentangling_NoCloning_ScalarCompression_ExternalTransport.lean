-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalTransport
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:04:20.074532+00:00
-- url     : https://prove2.me/theorems/37f2ff47-985c-4e21-8a45-352e6752937d
-- title:
--   External Transport
-- statement:
--   Definitions and structural lemmas for External Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/ExternalTransport.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalData
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000
end BPTCommutingProjectorModel
end Bounds
end QEC


