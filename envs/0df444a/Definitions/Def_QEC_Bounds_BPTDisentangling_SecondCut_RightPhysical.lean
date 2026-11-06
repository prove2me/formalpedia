-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_RightPhysical
-- name    : QEC_Bounds_BPTDisentangling_SecondCut_RightPhysical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:37:25.269853+00:00
-- url     : https://prove2.me/theorems/64912849-2256-46e9-910b-f0385d06030f
-- title:
--   Right Physical
-- statement:
--   Definitions and structural lemmas for Right Physical, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/RightPhysical.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_TensorFactor
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


