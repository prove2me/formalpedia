-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_LeftCompression
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_LeftCompression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:00:37.448523+00:00
-- url     : https://prove2.me/theorems/0311beaa-d4fb-41d8-9275-8138d1738d09
-- title:
--   Left Compression
-- statement:
--   Definitions and structural lemmas for Left Compression, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/LeftCompression.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompression
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
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


