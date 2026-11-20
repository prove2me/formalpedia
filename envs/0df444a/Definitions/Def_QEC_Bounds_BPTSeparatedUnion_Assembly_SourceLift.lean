-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_SourceLift
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_SourceLift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:25:29.321181+00:00
-- url     : https://prove2.me/theorems/8e7e21dc-d7ec-47eb-a187-660226db8cd6
-- title:
--   Source Lift
-- statement:
--   Definitions and structural lemmas for Source Lift, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/SourceLift.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_ProjectorLift
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorWitness
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


