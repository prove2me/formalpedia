-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
-- name    : QEC_Semantics_Dynamics_Davies_TraceBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:29:32.355945+00:00
-- url     : https://prove2.me/theorems/00833200-6a70-4663-9cd0-2b7167832cff
-- title:
--   Trace Bound
-- statement:
--   Definitions and structural lemmas for Trace Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/TraceBound.lean

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
namespace QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]
def squareSum (J : κ → Operator V) : Operator V := ∑ a, LinearMap.adjoint (J a) * J a
end
end QEC.Semantics.Davies


