-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Internal
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Internal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:34:40.945202+00:00
-- url     : https://prove2.me/theorems/c077d97d-1802-4a11-89ee-f5f21707df6f
-- title:
--   Internal
-- statement:
--   Definitions and structural lemmas for Internal, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Internal.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalAssembly
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


