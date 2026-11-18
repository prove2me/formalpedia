-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningComplement
-- name    : QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningComplement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T05:15:58.938921+00:00
-- url     : https://prove2.me/theorems/2268d442-f993-4a2a-8a31-d6cb764e0daa
-- title:
--   Intertwining Complement
-- statement:
--   Definitions and structural lemmas for Intertwining Complement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IntertwiningComplement.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningStatement
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ComplementIntertwiningCore
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


