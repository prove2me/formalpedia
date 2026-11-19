-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryRealization
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_IsometryRealization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T06:57:20.562412+00:00
-- url     : https://prove2.me/theorems/28c12384-6010-4fb3-b3aa-f7bf27f96255
-- title:
--   Isometry Realization
-- statement:
--   Definitions and structural lemmas for Isometry Realization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IsometryRealization.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IsometryCore
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


