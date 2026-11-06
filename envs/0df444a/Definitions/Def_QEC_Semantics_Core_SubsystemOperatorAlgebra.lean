-- Prove2me | Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
-- name    : QEC_Semantics_Core_SubsystemOperatorAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:10:03.900942+00:00
-- url     : https://prove2.me/theorems/ff7f0d87-7acd-4ab5-ac13-bedef37f9276
-- title:
--   Subsystem Operator Algebra
-- statement:
--   Definitions and structural lemmas for Subsystem Operator Algebra, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean

import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
namespace QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end
end QEC.Semantics.FiniteSubsystem


