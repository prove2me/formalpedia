-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
-- name    : QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:29:33.109198+00:00
-- url     : https://prove2.me/theorems/b4e49bfc-99d8-4400-89c9-b1d493002eff
-- title:
--   Projection Block
-- statement:
--   Definitions and structural lemmas for Projection Block, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftPhysical
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


