-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Conjugation
-- name    : QEC_Bounds_BPTDisentangling_Sectors_Conjugation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:19:52.806189+00:00
-- url     : https://prove2.me/theorems/b86f4ae4-0b3d-4639-9040-54d5b5a11083
-- title:
--   Conjugation
-- statement:
--   Definitions and structural lemmas for Conjugation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Conjugation.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
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


