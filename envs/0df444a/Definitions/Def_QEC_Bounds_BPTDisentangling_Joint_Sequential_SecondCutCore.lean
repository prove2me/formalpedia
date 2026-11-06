-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutCore
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:21:33.994752+00:00
-- url     : https://prove2.me/theorems/342277a5-6632-478f-884c-9851b6396c84
-- title:
--   Second Cut Core
-- statement:
--   Definitions and structural lemmas for Second Cut Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutCore.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
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


