-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Basic
-- name    : LeanPool_FormalLearningTheory_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:28.145992+00:00
-- url     : https://prove2.me/theorems/58a3c03c-397e-41f4-8c3a-ca900df4e81a
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Basic.lean

module
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
abbrev Concept (X : Type u) (Y : Type v) := X → Y
abbrev ConceptClass (X : Type u) (Y : Type v) := Set (Concept X Y)
class MeasurableHypotheses (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop where
  mem_measurable : ∀ h ∈ C, Measurable h
abbrev HypothesisSpace (X : Type u) (Y : Type v) := Set (Concept X Y)
abbrev Hypothesis (X : Type u) (Y : Type v) := Concept X Y
def TargetConcept (X : Type u) (Y : Type v) (C : ConceptClass X Y) := { c : Concept X Y // c ∈ C }
def IsProper (X : Type u) (Y : Type v) (C : ConceptClass X Y) (H : HypothesisSpace X Y) : Prop :=
  (H : Set (Concept X Y)) = (C : Set (Concept X Y))
structure InductiveBias (X : Type u) (Y : Type v) where
  /-- The hypothesis space the bias operates over -/
  hypotheses : HypothesisSpace X Y
  /-- Preference score: lower is more preferred. Could be complexity, prior probability, etc. -/
  preference : Concept X Y → ℝ
  /-- Hypotheses outside the space are not preferred over those inside:
      everything outside H is penalized at least as much as anything inside H.
      This works for both MDL (description length) and Bayesian (-log prior) readings. -/
  not_preferred : ∀ h, h ∉ hypotheses → ∀ h' ∈ hypotheses, preference h' ≤ preference h
structure VersionSpace (X : Type u) (Y : Type v) where
  /-- The full hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- Data seen so far: list of (input, label) pairs -/
  data : List (X × Y)
  /-- The consistent subset - hypotheses that agree with all data -/
  consistent : Set (Concept X Y)
  /-- Consistency condition: every consistent hypothesis is in H and agrees with data -/
  consistent_sub : consistent ⊆ hypotheses
  consistent_agrees : ∀ h ∈ consistent, ∀ p ∈ data, h p.1 = p.2
def Realizable (X : Type u) (Y : Type v) (C : ConceptClass X Y) (H : HypothesisSpace X Y) : Prop :=
  C ⊆ H
def Agnostic (X : Type u) (Y : Type v) (C : ConceptClass X Y) (H : HypothesisSpace X Y) : Prop :=
  C = C ∧ H = H
def LossFunction (Y : Type v) := Y → Y → ℝ
noncomputable def zeroOneLoss (Y : Type v) [DecidableEq Y] : LossFunction Y :=
  fun y₁ y₂ => if y₁ = y₂ then 0 else 1
noncomputable def squaredLoss : LossFunction ℝ :=
  fun y₁ y₂ => (y₁ - y₂) ^ 2


