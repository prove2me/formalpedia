-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
-- name    : QEC_Semantics_Instruments_TensorPower_FirstMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:51:50.515363+00:00
-- url     : https://prove2.me/theorems/dfb2ccb9-e85c-4245-a5ff-3da0a5965467
-- title:
--   First Moment
-- statement:
--   Definitions and structural lemmas for First Moment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
set_option autoImplicit false
universe u v w
namespace QEC
namespace Semantics
open scoped BigOperators
noncomputable section
namespace FiniteInstrument
def tensorPowerRejectedCount {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts : Nat)
    (history : tensorPowerHistory Ω attempts) : Nat :=
  attempts - (tensorPowerAcceptedIndices accepts attempts history).card
noncomputable def tensorPowerRejectedFirstMoment
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (rho : DensityOperator H)
    (_rhoUnit : DensityOperator (tensorPowerCarrier H 0)) (attempts : Nat) : ℝ :=
  ∑ history : tensorPowerHistory Ω attempts,
    (tensorPowerRejectedCount accepts attempts history : ℝ) *
      tensorPowerBornProduct I rho attempts history
end FiniteInstrument
end
end Semantics
end QEC


