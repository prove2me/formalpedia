-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_FirstCutBlock
-- name    : QEC_Bounds_BPTDisentangling_FirstCutBlock
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:20:44.766137+00:00
-- url     : https://prove2.me/theorems/6d12968c-2385-451f-a686-0f20fa05c9b7
-- title:
--   First Cut Block
-- statement:
--   Definitions and structural lemmas for First Cut Block, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FirstCutBlock.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Conjugation
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


