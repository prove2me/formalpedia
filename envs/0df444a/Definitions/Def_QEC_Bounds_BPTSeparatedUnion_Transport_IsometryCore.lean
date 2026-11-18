-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryCore
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_IsometryCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T05:41:33.492851+00:00
-- url     : https://prove2.me/theorems/1033943d-a109-4b6b-a057-60c87a100943
-- title:
--   Isometry Core
-- statement:
--   Definitions and structural lemmas for Isometry Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IsometryCore.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryCoordinates
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


