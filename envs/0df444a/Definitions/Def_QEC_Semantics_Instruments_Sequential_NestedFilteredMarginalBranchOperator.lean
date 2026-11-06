-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
-- name    : QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:45:48.77924+00:00
-- url     : https://prove2.me/theorems/a364b2b9-7e76-4bed-b6ff-2bc4c9180f33
-- title:
--   Nested Filtered Marginal Branch Operator
-- statement:
--   Definitions and structural lemmas for Nested Filtered Marginal Branch Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/NestedFilteredMarginalBranchOperator.lean

import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_FilteredMarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Sequential_FilteredBranchOperator
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
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
noncomputable def filteredBranchOperatorSum
    (J : FiniteInstrument kappaTwo Xi K L)
    (predicate : Xi -> Prop) [DecidablePred predicate]
    (A : Operator K) : Operator L :=
  ∑ outcome : Xi,
    if predicate outcome then J.branchOperator outcome A else 0
noncomputable def nestedFilteredPredecessorCoordinateOperator
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (path : nestedTensorPath branches depth)
    (A : Operator H) : Operator K :=
  nestedTensorCoordinateOperator K branches depth path
    (∑ outcome : Omega,
      if predicate outcome then I.branchOperator outcome A else 0)
noncomputable def bindNestedFilteredCoordinateOperator
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (path : nestedTensorPath branches depth)
    (A : Operator H) : Operator L :=
  nestedTensorCoordinateOperator L branches depth path
    (∑ outcome : Sigma fun _ : Omega => nestedTensorHistory Xi branches depth,
      if firstPredicate outcome.1 ∧
          secondPredicate
            (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
        (I.bind (fun _ => nestedTensorPower J branches depth)).branchOperator
          outcome A
      else 0)
end FiniteInstrument
end
end Semantics
end QEC


