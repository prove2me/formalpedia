-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
-- name    : QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:40:12.072038+00:00
-- url     : https://prove2.me/theorems/d6926f2a-723d-46c4-bdbe-dede011db595
-- title:
--   Residual Projection
-- statement:
--   Definitions and structural lemmas for Residual Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/ResidualProjection.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutProjection
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


