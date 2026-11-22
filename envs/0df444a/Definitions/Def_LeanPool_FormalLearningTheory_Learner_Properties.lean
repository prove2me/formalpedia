-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Learner_Properties
-- name    : LeanPool_FormalLearningTheory_Learner_Properties
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:24.495501+00:00
-- url     : https://prove2.me/theorems/d415ff2c-f974-4624-b3c6-9409f62d7b82
-- title:
--   Properties
-- statement:
--   Definitions and structural lemmas for Properties, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Properties.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
def IsIterative {X : Type u} {Y : Type v} (L : GoldLearner X Y) : Prop :=
  ∃ step : Concept X Y → (X × Y) → Concept X Y,
    ∀ (data : List (X × Y)) (xy : X × Y),
      L.conjecture (data ++ [xy]) = step (L.conjecture data) xy
def IsSetDriven {X : Type u} {Y : Type v} [DecidableEq X] [DecidableEq Y]
    (L : GoldLearner X Y) : Prop :=
  ∀ (data₁ data₂ : List (X × Y)),
    data₁.toFinset = data₂.toFinset → L.conjecture data₁ = L.conjecture data₂
def IsConsistent {X : Type u} {Y : Type v} (L : GoldLearner X Y) : Prop :=
  ∀ (data : List (X × Y)),
    ∀ p ∈ data, (L.conjecture data) p.1 = p.2
def IsConservative {X : Type u} {Y : Type v} (L : GoldLearner X Y) : Prop :=
  ∀ (data : List (X × Y)) (xy : X × Y),
    (L.conjecture data) xy.1 = xy.2 →
      L.conjecture (data ++ [xy]) = L.conjecture data
structure ProbabilisticLearner (X : Type u) (Y : Type v) where
  /-- The hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- Randomized learning: seed → sample → hypothesis -/
  learn : {m : ℕ} → ℕ → (Fin m → X × Y) → Concept X Y
structure TeamLearner (X : Type u) (Y : Type v) (n : ℕ) where
  /-- The team members -/
  team : Fin n → GoldLearner X Y


