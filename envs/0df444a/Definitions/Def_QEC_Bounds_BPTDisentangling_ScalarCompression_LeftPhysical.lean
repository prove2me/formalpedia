-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftPhysical
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_LeftPhysical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:43:19.224005+00:00
-- url     : https://prove2.me/theorems/8a17986e-3884-41e2-be69-0086ccb6c006
-- title:
--   Left Physical
-- statement:
--   Definitions and structural lemmas for Left Physical, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftPhysical.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftProbe
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


