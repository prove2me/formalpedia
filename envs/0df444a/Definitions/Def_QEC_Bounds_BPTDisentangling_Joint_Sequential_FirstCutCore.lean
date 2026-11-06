-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutCore
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:21:08.113609+00:00
-- url     : https://prove2.me/theorems/5cd76103-5486-4378-9bb9-7f320a3111d8
-- title:
--   First Cut Core
-- statement:
--   Definitions and structural lemmas for First Cut Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/FirstCutCore.lean

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


