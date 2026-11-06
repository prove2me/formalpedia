-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
-- name    : QEC_Semantics_Instruments_TensorPower_BornMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:50:31.806452+00:00
-- url     : https://prove2.me/theorems/dce6e5ca-e74b-4b16-b7d5-eb09938104f6
-- title:
--   Born Mass
-- statement:
--   Definitions and structural lemmas for Born Mass, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
set_option autoImplicit false
universe u v w x y
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
namespace FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
noncomputable def rawBranchOperator (I : FiniteInstrument κ Ω H K) (index : κ)
    (A : Operator H) : Operator K :=
  (I.kraus.operator index).comp
    (A.comp (LinearMap.adjoint (I.kraus.operator index)))
noncomputable def rawBornWeight (I : FiniteInstrument κ Ω H K) (index : κ)
    (rho : DensityOperator H) : ℝ :=
  Complex.re (LinearMap.trace Complex K (I.rawBranchOperator index rho.toOperator))
section Tensor
variable {κ' : Type x} [Fintype κ']
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
end Tensor
noncomputable def tensorPowerProductInput (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    (attempts : Nat) → DensityOperator (tensorPowerCarrier H attempts)
  | 0 => rhoUnit
  | attempts + 1 => DensityOperator.tensorDensity rho
      (tensorPowerProductInput rho rhoUnit attempts)
noncomputable def tensorPowerRawBornProduct (I : FiniteInstrument κ Ω H K)
    (rho : DensityOperator H) :
    (attempts : Nat) → tensorPowerHistory κ attempts → ℝ
  | 0, _ => 1
  | attempts + 1, history =>
      I.rawBornWeight history.1 rho * tensorPowerRawBornProduct I rho attempts history.2
noncomputable def tensorPowerBornProduct (I : FiniteInstrument κ Ω H K)
    (rho : DensityOperator H) :
    (attempts : Nat) → tensorPowerHistory Ω attempts → ℝ
  | 0, _ => 1
  | attempts + 1, history =>
      I.bornWeight history.1 rho * tensorPowerBornProduct I rho attempts history.2
noncomputable def tensorPowerEnoughMass (I : FiniteInstrument κ Ω H K)
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) : ℝ :=
  ∑ history ∈ Finset.univ.filter
      (fun history => required ≤ (tensorPowerAcceptedIndices accepts attempts history).card),
    (I.tensorPower attempts).bornWeight history rho
noncomputable def tensorPowerShortageMass (I : FiniteInstrument κ Ω H K)
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) : ℝ :=
  ∑ history ∈ Finset.univ.filter
      (fun history => (tensorPowerAcceptedIndices accepts attempts history).card < required),
    (I.tensorPower attempts).bornWeight history rho
section DependentMass
variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
end DependentMass
end FiniteInstrument
end
end Semantics
end QEC


