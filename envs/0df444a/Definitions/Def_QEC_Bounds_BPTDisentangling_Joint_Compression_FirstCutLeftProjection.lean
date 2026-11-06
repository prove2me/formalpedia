-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutLeftProjection
-- name    : QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutLeftProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:27:48.336422+00:00
-- url     : https://prove2.me/theorems/4603c0ea-0902-4011-9042-a09ba54ad426
-- title:
--   First Cut Left Projection
-- statement:
--   Definitions and structural lemmas for First Cut Left Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutLeftProjection.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_Transport
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


