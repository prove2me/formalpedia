-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ExteriorAction
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_ExteriorAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:16:38.885738+00:00
-- url     : https://prove2.me/theorems/4a004a1f-90ec-4dba-8d09-28be5be6d16e
-- title:
--   Exterior Action
-- statement:
--   Definitions and structural lemmas for Exterior Action, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/ExteriorAction.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_FourFactor
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


