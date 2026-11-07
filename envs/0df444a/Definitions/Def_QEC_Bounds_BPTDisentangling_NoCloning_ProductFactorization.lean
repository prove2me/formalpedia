-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductFactorization
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ProductFactorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:31:11.395284+00:00
-- url     : https://prove2.me/theorems/f8b66c13-3919-4d82-b829-87866f12ca74
-- title:
--   Product Factorization
-- statement:
--   Definitions and structural lemmas for Product Factorization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ProductFactorization.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductUnitary
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
namespace BPTCommutingProjectorModel
end BPTCommutingProjectorModel
end Bounds
end QEC


