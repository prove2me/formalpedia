-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyDisentangling
-- name    : QEC_Bounds_BPTDisentangling_Assembly_AssemblyDisentangling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T07:09:29.86038+00:00
-- url     : https://prove2.me/theorems/1d4300be-2d33-4e74-9c19-f9038db4f89a
-- title:
--   Assembly Disentangling
-- statement:
--   Definitions and structural lemmas for Assembly Disentangling, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyDisentangling.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
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


