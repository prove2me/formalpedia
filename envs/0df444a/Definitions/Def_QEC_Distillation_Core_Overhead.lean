-- Prove2me | Definitions.Def_QEC_Distillation_Core_Overhead
-- name    : QEC_Distillation_Core_Overhead
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:16:37.128197+00:00
-- url     : https://prove2.me/theorems/1b7ba1dd-551a-41b6-9153-a0c5818594f1
-- title:
--   Overhead
-- statement:
--   Definitions and structural lemmas for Overhead, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
set_option autoImplicit false
universe u
namespace QEC.Distillation
open Semantics
structure DistillationProtocolFamily
    (Resource Input Output Index : Type u)
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output] where
  targetError : Index → ℝ
  protocol : (index : Index) →
    MagicStateDistillationProtocol Resource Input Output
  outputResourceCount : Index → Nat
  outputResourceCount_pos : ∀ index, 0 < outputResourceCount index
  successfulOutputError_le_targetError : ∀ index,
    (protocol index).successfulOutputError ≤ targetError index
namespace DistillationProtocolFamily
variable {Resource Input Output Index : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]
def inputResourceCount
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) : Nat :=
  (family.protocol index).run.resourceCount
noncomputable def inputOutputRatio
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) : ℝ :=
  family.inputResourceCount index / family.outputResourceCount index
noncomputable def successfulOutputCost
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) : ℝ :=
  family.inputResourceCount index /
    (family.outputResourceCount index *
      (family.protocol index).run.successProbability)
end DistillationProtocolFamily
def SuccessfulOutputCostBound
    {Resource Input Output Index : Type u}
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) (bound : ℝ) : Prop :=
  0 < (family.protocol index).run.successProbability ∧
    family.successfulOutputCost index ≤ bound
def PolylogarithmicOverhead
    {Resource Input Output Index : Type u}
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (family : DistillationProtocolFamily Resource Input Output Index)
    (gamma coefficient : ℝ) : Prop :=
  0 ≤ coefficient ∧ ∀ index,
    0 < family.targetError index → family.targetError index < 1 →
    0 < (family.protocol index).run.successProbability ∧
      family.successfulOutputCost index ≤ coefficient *
        (Real.log (1 / family.targetError index)) ^ gamma
def BoundedInputOutputRatio
    {Resource Input Output Index : Type u}
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (family : DistillationProtocolFamily Resource Input Output Index)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index,
    0 < family.targetError index → family.targetError index < 1 →
    family.inputOutputRatio index ≤ bound
structure SpaceOverhead where
  value : ℝ
  value_nonneg : 0 ≤ value
structure CircuitTimeOverhead where
  value : ℝ
  value_nonneg : 0 ≤ value
structure DecoderComplexityOverhead where
  value : ℝ
  value_nonneg : 0 ≤ value
end QEC.Distillation


