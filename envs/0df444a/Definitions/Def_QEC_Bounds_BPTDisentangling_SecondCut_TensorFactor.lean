-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_TensorFactor
-- name    : QEC_Bounds_BPTDisentangling_SecondCut_TensorFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:36:20.975192+00:00
-- url     : https://prove2.me/theorems/8520fc3e-6b8e-4677-bc11-c1a85f45301b
-- title:
--   Tensor Factor
-- statement:
--   Definitions and structural lemmas for Tensor Factor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/TensorFactor.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
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


