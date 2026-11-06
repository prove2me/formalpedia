-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
-- name    : QEC_Semantics_Instruments_TensorPower_BranchOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:51:50.367893+00:00
-- url     : https://prove2.me/theorems/1b8eb3e6-de58-4329-ac59-34a0c8a7d910
-- title:
--   Branch Operator
-- statement:
--   Definitions and structural lemmas for Branch Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
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
noncomputable def tensorPowerBranchOperatorProduct
    (branch : Ω → Operator K)
    (unit : Operator (tensorPowerCarrier K 0)) :
    (attempts : Nat) → tensorPowerHistory Ω attempts →
      Operator (tensorPowerCarrier K attempts)
  | 0, _ => unit
  | attempts + 1, history =>
      TensorProduct.map (branch history.1)
        (tensorPowerBranchOperatorProduct branch unit attempts history.2)
noncomputable def tensorPowerBranchOperatorMatrixEntryProduct
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (branch : Ω → Operator K)
    (unit : Operator (tensorPowerCarrier K 0)) :
    (attempts : Nat) → tensorPowerHistory Ω attempts →
      tensorPowerHistory β attempts → tensorPowerHistory β attempts → Complex
  | 0, _, left, right =>
      inner Complex (tensorPowerBasis basis 0 left)
        (unit (tensorPowerBasis basis 0 right))
  | attempts + 1, history, left, right =>
      inner Complex (basis left.1) (branch history.1 (basis right.1)) *
        tensorPowerBranchOperatorMatrixEntryProduct basis branch unit attempts
          history.2 left.2 right.2
section Tensor
variable {κ' : Type x} [Fintype κ']
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
end Tensor
section DependentBind
variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
end DependentBind
section UnitFirstBind
variable {κ' : Type x} [Fintype κ']
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
end UnitFirstBind
end FiniteInstrument
end
end Semantics
end QEC


