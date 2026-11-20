-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Core
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:34:37.705383+00:00
-- url     : https://prove2.me/theorems/8c15e98c-ee50-4f5a-8d7c-d945d87ebe79
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/Core.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_SourceLift
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


