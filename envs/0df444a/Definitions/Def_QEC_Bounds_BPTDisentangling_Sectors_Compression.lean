-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Compression
-- name    : QEC_Bounds_BPTDisentangling_Sectors_Compression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:21:57.291004+00:00
-- url     : https://prove2.me/theorems/63429662-8f59-46e9-bf0e-ae6ba26c8c3d
-- title:
--   Compression
-- statement:
--   Definitions and structural lemmas for Compression, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Compression.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_FirstCutBlock
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


