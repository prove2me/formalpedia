-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:27:47.24584+00:00
-- url     : https://prove2.me/theorems/0c3830b7-3998-4f0d-a3e5-8bdc085dc68b
-- title:
--   Partial Trace
-- statement:
--   Definitions and structural lemmas for Partial Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Transport
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


