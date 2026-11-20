-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RightIntertwining
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_RightIntertwining
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:09:19.176676+00:00
-- url     : https://prove2.me/theorems/b4954f96-39af-4a5a-9004-359e23badf9f
-- title:
--   Right Intertwining
-- statement:
--   Definitions and structural lemmas for Right Intertwining, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/RightIntertwining.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Isometry
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningCore
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


