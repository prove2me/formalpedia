-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
-- name    : QEC_Semantics_Dynamics_Davies_Stationarity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:55:55.99321+00:00
-- url     : https://prove2.me/theorems/ec3e07f6-9349-494b-b86e-2a597d8f4cd7
-- title:
--   Stationarity
-- statement:
--   Definitions and structural lemmas for Stationarity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
set_option autoImplicit false
namespace QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
def weightedJump {κ : Type*} (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (a : κ × Frequency e) : Operator V :=
  (Real.sqrt (rate a.1 a.2) : ℂ) • frequencyComponent b e (A a.1) a.2.val
end
end QEC.Semantics.Davies


