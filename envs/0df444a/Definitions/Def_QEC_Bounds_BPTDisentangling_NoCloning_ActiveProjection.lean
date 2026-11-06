-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActiveProjection
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ActiveProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:46:37.37365+00:00
-- url     : https://prove2.me/theorems/35750beb-3d01-4470-8817-aa2944e97a62
-- title:
--   Active Projection
-- statement:
--   Definitions and structural lemmas for Active Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Factorization
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


