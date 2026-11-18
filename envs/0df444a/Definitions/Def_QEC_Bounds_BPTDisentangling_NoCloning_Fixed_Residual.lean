-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Residual
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Residual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:14:24.665179+00:00
-- url     : https://prove2.me/theorems/5333dfff-638d-4a8d-aa01-51116d7ec882
-- title:
--   Residual
-- statement:
--   Definitions and structural lemmas for Residual, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/Residual.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_RankOne
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


