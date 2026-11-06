-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
-- name    : QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:41:55.001643+00:00
-- url     : https://prove2.me/theorems/4cb2ef6d-1ae7-4717-8f1c-88a437958a3f
-- title:
--   Marginal Branch Operator
-- statement:
--   Definitions and structural lemmas for Marginal Branch Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/MarginalBranchOperator.lean

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u v w x y
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators
noncomputable section
namespace FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
noncomputable def outcomeBranchInstrument
    (I : FiniteInstrument kappa Omega H K) (outcome : Omega) :
    FiniteInstrument kappa Omega H K where
  kraus :=
    { operator := fun index =>
        if I.observe index = outcome then I.kraus.operator index else 0 }
  observe := fun _ => outcome
end FiniteInstrument
end
end Semantics
end QEC


