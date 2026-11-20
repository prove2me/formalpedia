-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Intertwining
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_Intertwining
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:16:46.231949+00:00
-- url     : https://prove2.me/theorems/f712d7d5-ddfa-46d7-9e00-fb65fb379197
-- title:
--   Intertwining
-- statement:
--   Definitions and structural lemmas for Intertwining, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/Intertwining.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_IntertwiningCore
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


