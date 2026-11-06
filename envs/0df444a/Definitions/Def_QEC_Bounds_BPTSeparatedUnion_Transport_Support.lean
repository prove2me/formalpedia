-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_Support
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:15:32.98739+00:00
-- url     : https://prove2.me/theorems/ebb68423-9fe5-4d17-acc4-f770829d7a66
-- title:
--   Support
-- statement:
--   Definitions and structural lemmas for Support, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/Support.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
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


