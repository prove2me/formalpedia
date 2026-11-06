-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutJoint
-- name    : QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutJoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:04:39.618412+00:00
-- url     : https://prove2.me/theorems/678e0307-f19e-43e3-ad43-3cd98060b6df
-- title:
--   Second Cut Joint
-- statement:
--   Definitions and structural lemmas for Second Cut Joint, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutJoint.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutActive
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutEquality
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutJointData
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


