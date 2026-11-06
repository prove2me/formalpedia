-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
-- name    : QEC_Semantics_Dynamics_Davies_Pinching
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:56:32.527854+00:00
-- url     : https://prove2.me/theorems/60db6880-8e78-40f2-a549-f77cee4af598
-- title:
--   Pinching
-- statement:
--   Definitions and structural lemmas for Pinching, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Pinching.lean

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
set_option autoImplicit false
namespace QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end
end QEC.Semantics.Davies


