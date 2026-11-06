-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutFactorNonzero
-- name    : QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutFactorNonzero
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:36:14.120652+00:00
-- url     : https://prove2.me/theorems/c074292b-3cec-4432-95c3-40f69ab7a005
-- title:
--   First Cut Factor Nonzero
-- statement:
--   Definitions and structural lemmas for First Cut Factor Nonzero, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutFactorNonzero.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeNonzero
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


