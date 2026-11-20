-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_SelectedTensorCompression
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_SelectedTensorCompression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:33:31.810169+00:00
-- url     : https://prove2.me/theorems/70ecbdce-5b69-4899-8840-f3e1ff617713
-- title:
--   Selected Tensor Compression
-- statement:
--   Definitions and structural lemmas for Selected Tensor Compression, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/SelectedTensorCompression.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Intertwining
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorBridge
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


