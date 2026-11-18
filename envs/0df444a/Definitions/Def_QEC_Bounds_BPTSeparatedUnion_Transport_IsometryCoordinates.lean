-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryCoordinates
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_IsometryCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T05:36:07.904194+00:00
-- url     : https://prove2.me/theorems/46fb4e5c-a1de-40a3-9fc8-17f40cf6d3c7
-- title:
--   Isometry Coordinates
-- statement:
--   Definitions and structural lemmas for Isometry Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IsometryCoordinates.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryActive
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


