-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeNonzero
-- name    : QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeNonzero
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:34:43.832788+00:00
-- url     : https://prove2.me/theorems/cf864dad-52db-4967-b1eb-e4ac48cb712f
-- title:
--   First Cut Code Nonzero
-- statement:
--   Definitions and structural lemmas for First Cut Code Nonzero, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutCodeNonzero.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutLeftProjection
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


