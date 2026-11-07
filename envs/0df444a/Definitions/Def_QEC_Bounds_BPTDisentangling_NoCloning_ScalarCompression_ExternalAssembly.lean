-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalAssembly
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:13:15.073807+00:00
-- url     : https://prove2.me/theorems/4d75c69f-6e71-49f8-866d-b46b9886e13b
-- title:
--   External Assembly
-- statement:
--   Definitions and structural lemmas for External Assembly, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/ExternalAssembly.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalTransport
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


