-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
-- name    : QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:09:53.116019+00:00
-- url     : https://prove2.me/theorems/db6724aa-19c1-4752-95ed-63113958773e
-- title:
--   Assembly Transport
-- statement:
--   Definitions and structural lemmas for Assembly Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyTransport.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransportCore
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


