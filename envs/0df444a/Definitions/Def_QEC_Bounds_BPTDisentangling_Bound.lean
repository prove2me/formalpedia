-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Bound
-- name    : QEC_Bounds_BPTDisentangling_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:13:36.9052+00:00
-- url     : https://prove2.me/theorems/7ecb407f-3f2e-483a-8310-4909b4bf4b5a
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Bound.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyDisentangling
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
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


