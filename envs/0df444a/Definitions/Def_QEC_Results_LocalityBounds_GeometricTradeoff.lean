-- Prove2me | Definitions.Def_QEC_Results_LocalityBounds_GeometricTradeoff
-- name    : QEC_Results_LocalityBounds_GeometricTradeoff
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:22:30.072011+00:00
-- url     : https://prove2.me/theorems/7e29c6e7-d90c-4eaf-8118-5bd9522023bb
-- title:
--   Geometric Tradeoff
-- statement:
--   Definitions and structural lemmas for Geometric Tradeoff, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/GeometricTradeoff.lean

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open scoped BigOperators
universe v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


