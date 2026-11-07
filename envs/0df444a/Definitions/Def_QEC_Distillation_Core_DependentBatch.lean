-- Prove2me | Definitions.Def_QEC_Distillation_Core_DependentBatch
-- name    : QEC_Distillation_Core_DependentBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:26:47.258386+00:00
-- url     : https://prove2.me/theorems/e8dc3632-b40a-425d-b376-1f1856d93e5f
-- title:
--   Dependent Batch
-- statement:
--   Definitions and structural lemmas for Dependent Batch, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/DependentBatch.lean

import Definitions.Def_QEC_Distillation_Core_Overhead
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.DependentBatch
open Semantics
open scoped BigOperators
universe u v
def parentPortTranspose (Parent : Type u) (Port : Type v) :
    Parent × Port ≃ Port × Parent where
  toFun := fun pair => (pair.2, pair.1)
  invFun := fun pair => (pair.2, pair.1)
  left_inv := by
    intro pair
    rfl
  right_inv := by
    intro pair
    rfl
def transposeRouting (n k : Nat) : Fin n × Fin k ≃ Fin k × Fin n :=
  parentPortTranspose (Fin n) (Fin k)
def childInputSlot {Parent Port : Type*} (port : Port) (parent : Parent) :
    Parent × Port :=
  (parent, port)
structure FiniteFlaggedBatch (Port : Type u) (Outcome : Type v)
    [Fintype Port] [Fintype Outcome] where
  weight : Outcome → ℝ
  weight_nonneg : ∀ outcome, 0 ≤ weight outcome
  total_weight : ∑ outcome, weight outcome = 1
  accepted : Outcome → Port → Bool
def acceptedPortCount {Port : Type u} {Outcome : Type v}
    [Fintype Port] [Fintype Outcome]
    (batch : FiniteFlaggedBatch Port Outcome) (outcome : Outcome) : Nat :=
  (Finset.univ.filter fun port => batch.accepted outcome port = true).card
noncomputable def expectedAcceptedPorts {Port : Type u} {Outcome : Type v}
    [Fintype Port] [Fintype Outcome]
    (batch : FiniteFlaggedBatch Port Outcome) : ℝ :=
  ∑ outcome, batch.weight outcome * acceptedPortCount batch outcome
noncomputable def pooledExpectedAcceptedPorts {Port : Type u} {Outcome : Type v}
    [Fintype Port] [Fintype Outcome] (count : Nat)
    (pool : Fin count → FiniteFlaggedBatch Port Outcome) : ℝ :=
  ∑ grid, expectedAcceptedPorts (pool grid)
noncomputable def typedInputOutputRatio (InputSlots OutputSlots : Type*)
    [Fintype InputSlots] [Fintype OutputSlots] : ℝ :=
  (Fintype.card InputSlots : ℝ) / Fintype.card OutputSlots
noncomputable def typedSuccessfulOutputCost (InputSlots OutputSlots : Type*)
    [Fintype InputSlots] [Fintype OutputSlots] (yieldFactor : NNReal) : ℝ :=
  typedInputOutputRatio InputSlots OutputSlots / yieldFactor
def typedPolylogCostBound {Index : Type*}
    (InputSlots OutputSlots : Index → Type*)
    [∀ index, Fintype (InputSlots index)]
    [∀ index, Fintype (OutputSlots index)]
    (targetError : Index → ℝ) (yieldFactor : Index → NNReal)
    (gamma coefficient : ℝ) : Prop :=
  0 ≤ coefficient ∧ ∀ index,
    0 < targetError index → targetError index < 1 →
      0 < (yieldFactor index : ℝ) ∧
        typedSuccessfulOutputCost (InputSlots index) (OutputSlots index)
          (yieldFactor index) ≤ coefficient *
            Real.rpow (Real.log (1 / targetError index)) gamma
def physicalPolylogarithmicExpectedYieldOverhead {Index : Type*}
    (InputSlots OutputSlots : Index → Type*)
    [∀ index, Fintype (InputSlots index)]
    [∀ index, Fintype (OutputSlots index)]
    (targetError actualOutputError : Index → ℝ) (yieldFactor : Index → NNReal)
    (gamma coefficient : ℝ) : Prop :=
  0 ≤ coefficient ∧ ∀ index,
    0 < targetError index → targetError index < 1 →
      actualOutputError index ≤ targetError index ∧
        0 < (yieldFactor index : ℝ) ∧
          typedSuccessfulOutputCost (InputSlots index) (OutputSlots index)
            (yieldFactor index) ≤ coefficient *
              Real.rpow (Real.log (1 / targetError index)) gamma
end QEC.Distillation.DependentBatch


