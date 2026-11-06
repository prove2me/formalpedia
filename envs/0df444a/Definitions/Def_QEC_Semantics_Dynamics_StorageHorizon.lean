-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_StorageHorizon
-- name    : QEC_Semantics_Dynamics_StorageHorizon
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:07:10.041033+00:00
-- url     : https://prove2.me/theorems/f10bf0be-45a1-481d-9a10-2766fa340cae
-- title:
--   Storage Horizon
-- statement:
--   Definitions and structural lemmas for Storage Horizon, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/StorageHorizon.lean

import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
set_option autoImplicit false
noncomputable section
namespace QEC.Semantics
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
end QEC.Semantics


