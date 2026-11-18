-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Product
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Product
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:49:51.46956+00:00
-- url     : https://prove2.me/theorems/50526b6b-9cd1-4eeb-a854-4b64f60c67d5
-- title:
--   Product
-- statement:
--   Definitions and structural lemmas for Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/Product.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductData
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


