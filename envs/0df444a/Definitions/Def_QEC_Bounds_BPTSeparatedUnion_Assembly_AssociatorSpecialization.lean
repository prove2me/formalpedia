-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorSpecialization
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorSpecialization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:48:58.29045+00:00
-- url     : https://prove2.me/theorems/9c813572-100c-4b45-9064-08405d8fd06c
-- title:
--   Associator Specialization
-- statement:
--   Definitions and structural lemmas for Associator Specialization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/AssociatorSpecialization.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open scoped TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


