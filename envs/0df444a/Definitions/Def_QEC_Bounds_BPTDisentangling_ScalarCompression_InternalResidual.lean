-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:55:41.349785+00:00
-- url     : https://prove2.me/theorems/ef39087f-63c0-4ceb-9e44-bc2811bcc6a3
-- title:
--   Internal Residual
-- statement:
--   Definitions and structural lemmas for Internal Residual, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/InternalResidual.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOneTransport
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


