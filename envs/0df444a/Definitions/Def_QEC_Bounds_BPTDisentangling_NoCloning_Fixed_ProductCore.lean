-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCore
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:21:24.923398+00:00
-- url     : https://prove2.me/theorems/ebd7298b-d8eb-4b20-9629-b22f0f7f1c4c
-- title:
--   Product Core
-- statement:
--   Definitions and structural lemmas for Product Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/ProductCore.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCoreData
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductFactorization
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


