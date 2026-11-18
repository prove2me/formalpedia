-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningTensor
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningTensor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T05:29:25.294639+00:00
-- url     : https://prove2.me/theorems/f038d15d-030e-471b-a55b-827293f90202
-- title:
--   Intertwining Tensor
-- statement:
--   Definitions and structural lemmas for Intertwining Tensor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IntertwiningTensor.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningComplement
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorActiveStatement
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


