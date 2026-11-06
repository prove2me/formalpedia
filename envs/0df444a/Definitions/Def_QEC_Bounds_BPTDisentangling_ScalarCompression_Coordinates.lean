-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Coordinates
-- name    : QEC_Bounds_BPTDisentangling_ScalarCompression_Coordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:40:36.255765+00:00
-- url     : https://prove2.me/theorems/9dfb651e-6af1-473f-8ac5-384023bf47ce
-- title:
--   Coordinates
-- statement:
--   Definitions and structural lemmas for Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Coordinates.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Core
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


