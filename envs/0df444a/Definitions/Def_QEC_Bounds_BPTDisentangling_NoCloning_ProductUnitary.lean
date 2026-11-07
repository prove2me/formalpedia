-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductUnitary
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ProductUnitary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:29:43.795417+00:00
-- url     : https://prove2.me/theorems/a33b513d-1d3d-49b4-b701-f8fdba7fb634
-- title:
--   Product Unitary
-- statement:
--   Definitions and structural lemmas for Product Unitary, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ProductUnitary.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
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


