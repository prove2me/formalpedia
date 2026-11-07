-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Aggregate
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Aggregate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:21:36.008201+00:00
-- url     : https://prove2.me/theorems/51b1a985-31f0-4f7d-9b0b-d2a0d9f71d27
-- title:
--   Aggregate
-- statement:
--   Definitions and structural lemmas for Aggregate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Aggregate.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_External
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
end BPTCommutingProjectorModel
end Bounds
end QEC


