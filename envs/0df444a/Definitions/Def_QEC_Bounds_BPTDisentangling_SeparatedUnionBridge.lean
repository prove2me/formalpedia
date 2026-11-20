-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
-- name    : QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:12:02.666919+00:00
-- url     : https://prove2.me/theorems/b3b1775f-0965-457e-b101-2054edf2caa6
-- title:
--   Separated Union Bridge
-- statement:
--   Definitions and structural lemmas for Separated Union Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
namespace BPTCommutingProjectorModel
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
end BPTCommutingProjectorModel
end Bounds
end QEC


