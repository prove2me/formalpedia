-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActualProduct
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ActualProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T23:51:57.039796+00:00
-- url     : https://prove2.me/theorems/f790376f-be84-4968-adaa-ef42ba9ee62e
-- title:
--   Actual Product
-- statement:
--   Definitions and structural lemmas for Actual Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActualProduct.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Product
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActualProductData
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


