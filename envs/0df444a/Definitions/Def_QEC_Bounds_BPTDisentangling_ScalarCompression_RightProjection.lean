-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RightProjection
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_RightProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:52:17.270834+00:00
-- url     : https://prove2.me/theorems/4353552f-f740-4634-b7a1-db2f096b7105
-- title:
--   Right Projection
-- statement:
--   Definitions and structural lemmas for Right Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/RightProjection.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneBlock
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


