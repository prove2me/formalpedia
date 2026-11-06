-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualScalar
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualScalar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T15:08:35.899472+00:00
-- url     : https://prove2.me/theorems/1b3a7e9c-35f9-4d3b-a493-2cce26e46e41
-- title:
--   Residual Scalar
-- statement:
--   Definitions and structural lemmas for Residual Scalar, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualScalar.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
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


