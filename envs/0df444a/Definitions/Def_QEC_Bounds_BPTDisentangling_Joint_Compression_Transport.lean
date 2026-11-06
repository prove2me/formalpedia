-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_Transport
-- name    : QEC_Bounds_BPTDisentangling_Joint_Compression_Transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:26:34.108201+00:00
-- url     : https://prove2.me/theorems/9556da3d-4d16-4930-84a3-57d51f214f24
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/Transport.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
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


