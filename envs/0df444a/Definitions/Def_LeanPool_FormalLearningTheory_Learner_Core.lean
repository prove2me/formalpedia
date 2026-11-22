-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
-- name    : LeanPool_FormalLearningTheory_Learner_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:52.280534+00:00
-- url     : https://prove2.me/theorems/d8805519-442a-4e0f-b3e0-cc7c7238c949
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Core.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
structure BatchLearner (X : Type u) (Y : Type v) where
  /-- The learner's hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- The learning algorithm: given a sample, produce a hypothesis -/
  learn : {m : ℕ} → (Fin m → X × Y) → Concept X Y
  /-- Output is in the hypothesis space -/
  output_in_H : ∀ {m : ℕ} (S : Fin m → X × Y), learn S ∈ hypotheses
structure OnlineLearner (X : Type u) (Y : Type v) where
  /-- Internal state type -/
  State : Type
  /-- Initial state -/
  init : State
  /-- Predict: given current state and new instance, output a prediction -/
  predict : State → X → Y
  /-- Update: given current state, instance, and revealed true label, update state -/
  update : State → X → Y → State
structure GoldLearner (X : Type u) (Y : Type v) where
  /-- The learner's conjecture given data seen so far -/
  conjecture : List (X × Y) → Concept X Y
class MeasurableBatchLearner (X : Type u) [MeasurableSpace X]
    (L : BatchLearner X Bool) : Prop where
  /-- Joint measurability of the evaluation map -/
  eval_measurable : ∀ (m : ℕ),
    Measurable (fun p : (Fin m → X × Bool) × X => L.learn p.1 p.2)


