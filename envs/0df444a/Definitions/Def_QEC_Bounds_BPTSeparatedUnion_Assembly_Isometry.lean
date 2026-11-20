-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Isometry
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_Isometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:03:23.741387+00:00
-- url     : https://prove2.me/theorems/28347efb-9c3d-4514-943e-683eac26428e
-- title:
--   Isometry
-- statement:
--   Definitions and structural lemmas for Isometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/Isometry.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_LeftCompression
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryRealization
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


