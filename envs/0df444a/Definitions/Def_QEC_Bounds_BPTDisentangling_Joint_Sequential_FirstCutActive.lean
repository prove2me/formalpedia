-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutActive
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutActive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:04:34.008212+00:00
-- url     : https://prove2.me/theorems/5b66c039-b553-4695-bdae-83e6b75fc220
-- title:
--   First Cut Active
-- statement:
--   Definitions and structural lemmas for First Cut Active, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/FirstCutActive.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_FirstCutBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveBlockTransports
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Factors
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutActiveData
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


