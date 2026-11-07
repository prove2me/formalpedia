-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalAssembly
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:12:11.13979+00:00
-- url     : https://prove2.me/theorems/0068222f-e524-477e-9e3d-d885685bf415
-- title:
--   Internal Assembly
-- statement:
--   Definitions and structural lemmas for Internal Assembly, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/InternalAssembly.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalTransport
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


