-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftProjection
-- name    : QEC_Bounds_BPTDisentangling_SecondCut_LeftProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:26:36.05918+00:00
-- url     : https://prove2.me/theorems/6b03b8bc-11a8-4ce1-a9ef-ca8500ed00b4
-- title:
--   Left Projection
-- statement:
--   Definitions and structural lemmas for Left Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
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


