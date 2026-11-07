-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalPhysical
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalPhysical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:10:13.050482+00:00
-- url     : https://prove2.me/theorems/dd3bfb03-1549-4c5b-ab1a-e69f8061d5fc
-- title:
--   Internal Physical
-- statement:
--   Definitions and structural lemmas for Internal Physical, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/InternalPhysical.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Core
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


