-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_External
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_External
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:49:16.095352+00:00
-- url     : https://prove2.me/theorems/bb6f0d03-2082-46c0-b262-13055d2fba50
-- title:
--   External
-- statement:
--   Definitions and structural lemmas for External, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/External.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Internal
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalAssembly
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000
end BPTCommutingProjectorModel
end Bounds
end QEC


