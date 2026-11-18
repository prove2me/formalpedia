-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryActive
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_IsometryActive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T05:22:18.980789+00:00
-- url     : https://prove2.me/theorems/b2db6227-321f-49f6-ba9e-ca231d2cef86
-- title:
--   Isometry Active
-- statement:
--   Definitions and structural lemmas for Isometry Active, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IsometryActive.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryStatement
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


