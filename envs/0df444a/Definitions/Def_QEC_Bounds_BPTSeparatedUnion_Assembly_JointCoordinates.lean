-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_JointCoordinates
-- name    : QEC_Bounds_BPTSeparatedUnion_Assembly_JointCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-18T06:52:09.587662+00:00
-- url     : https://prove2.me/theorems/9de215ad-ec4e-4dd8-a32b-edb0d3b71a48
-- title:
--   Joint Coordinates
-- statement:
--   Definitions and structural lemmas for Joint Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/JointCoordinates.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveBlockTransports
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
end BPTCommutingProjectorModel
end Bounds
end QEC


