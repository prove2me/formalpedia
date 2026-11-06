-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T15:04:36.790039+00:00
-- url     : https://prove2.me/theorems/007568c1-4585-4049-94c1-f2a21a186798
-- title:
--   Tensor
-- statement:
--   Definitions and structural lemmas for Tensor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Tensor.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalResidual
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


