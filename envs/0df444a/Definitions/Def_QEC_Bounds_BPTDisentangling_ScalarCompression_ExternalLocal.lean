-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalLocal
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalLocal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:57:45.27666+00:00
-- url     : https://prove2.me/theorems/310200fd-cc21-4a79-a361-73d624bb8c80
-- title:
--   External Local
-- statement:
--   Definitions and structural lemmas for External Local, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ExternalLocal.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
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


