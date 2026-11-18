-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_RankOne
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_Fixed_RankOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T22:26:23.839329+00:00
-- url     : https://prove2.me/theorems/767d6393-7c66-40a8-bd60-90302f71be42
-- title:
--   Rank One
-- statement:
--   Definitions and structural lemmas for Rank One, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/Fixed/RankOne.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_Compression
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1800000
end BPTCommutingProjectorModel
end Bounds
end QEC


