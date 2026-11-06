-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
-- name    : QEC_Bounds_BPTDisentangling_SecondCut_Projection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:25:45.514211+00:00
-- url     : https://prove2.me/theorems/4c9320a6-fb54-4cfb-8bc6-1aee11f46f91
-- title:
--   Projection
-- statement:
--   Definitions and structural lemmas for Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Projection.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Transport
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


