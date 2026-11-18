-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Common
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Common
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T22:03:22.515199+00:00
-- url     : https://prove2.me/theorems/f77f0f25-f7bd-43b6-87d4-bc2f0aaa794b
-- title:
--   Common
-- statement:
--   Definitions and structural lemmas for Common, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/Common.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ResidualData
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


