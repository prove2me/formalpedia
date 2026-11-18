-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
-- name    : QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:55:54.028202+00:00
-- url     : https://prove2.me/theorems/15c81a4c-106b-423e-b28d-879dc925bb3b
-- title:
--   Coordinate Transport
-- statement:
--   Definitions and structural lemmas for Coordinate Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/CoordinateTransport.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Core
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


