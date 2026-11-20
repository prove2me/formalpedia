-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransportBasic
-- name    : QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransportBasic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:04:15.295372+00:00
-- url     : https://prove2.me/theorems/b396b993-f32b-4904-aa39-cec593e9398a
-- title:
--   Assembly Transport Basic
-- statement:
--   Definitions and structural lemmas for Assembly Transport Basic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyTransportBasic.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
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


