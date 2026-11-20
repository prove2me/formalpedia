-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_ProjectorLift
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_ProjectorLift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:14:30.790417+00:00
-- url     : https://prove2.me/theorems/c4b69b2d-c778-4fab-940e-48e6c39152fc
-- title:
--   Projector Lift
-- statement:
--   Definitions and structural lemmas for Projector Lift, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/ProjectorLift.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RightIntertwining
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


