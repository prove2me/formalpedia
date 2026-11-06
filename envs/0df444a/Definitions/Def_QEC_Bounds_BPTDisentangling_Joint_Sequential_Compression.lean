-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Compression
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sequential_Compression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:51:09.374521+00:00
-- url     : https://prove2.me/theorems/730fe8a3-7914-4c3d-aaab-8da7375566c3
-- title:
--   Compression
-- statement:
--   Definitions and structural lemmas for Compression, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Compression.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Factors
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


