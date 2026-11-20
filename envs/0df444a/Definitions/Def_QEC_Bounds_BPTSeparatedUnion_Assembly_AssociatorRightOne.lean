-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorRightOne
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorRightOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:53:19.147058+00:00
-- url     : https://prove2.me/theorems/053c72b7-c643-4090-9105-2e56a2292246
-- title:
--   Associator Right One
-- statement:
--   Definitions and structural lemmas for Associator Right One, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/AssociatorRightOne.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorSpecialization
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open scoped TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


