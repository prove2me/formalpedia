-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:38:54.630165+00:00
-- url     : https://prove2.me/theorems/5131e9f8-986f-40fc-9ffe-75214d6a43f8
-- title:
--   Region Compression Raw
-- statement:
--   Definitions and structural lemmas for Region Compression Raw, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/RegionCompressionRaw.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_SelectedTensorCompression
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
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


