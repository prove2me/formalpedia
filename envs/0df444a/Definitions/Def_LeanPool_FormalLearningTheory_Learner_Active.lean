-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Learner_Active
-- name    : LeanPool_FormalLearningTheory_Learner_Active
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:28.255622+00:00
-- url     : https://prove2.me/theorems/8d4e5d8f-6528-4982-8dc2-0334cded3101
-- title:
--   Active
-- statement:
--   Definitions and structural lemmas for Active, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Active.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
structure ActiveLearner (X : Type u) (Y : Type v) where
  /-- The hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- Learning with membership oracle: produce a hypothesis -/
  learnMQ : MembershipOracle X Y → Concept X Y
  /-- Output is in hypothesis space -/
  output_in_H_MQ : ∀ (mq : MembershipOracle X Y), learnMQ mq ∈ hypotheses
def IsPassive {X : Type u} {Y : Type v} (L : BatchLearner X Y) : Prop := L = L
structure LearnerWithAdvice (X : Type u) (Y : Type v) (A : Type*) where
  /-- Base learner -/
  base : BatchLearner X Y
  /-- Advice-augmented learning: advice → sample → hypothesis -/
  learnWithAdvice : A → {m : ℕ} → (Fin m → X × Y) → Concept X Y
structure Teacher (X : Type u) (Y : Type v) where
  /-- The concept the teacher is teaching -/
  target : Concept X Y
  /-- Teaching strategy: choose next example given what's been shown -/
  teach : List (X × Y) → X × Y
def Teacher.teachingSequence {X : Type u} {Y : Type v}
    (T : Teacher X Y) : ℕ → List (X × Y)
  | 0 => []
  | n + 1 => let prev := T.teachingSequence n; prev ++ [T.teach prev]
def IsOptimalTeacher {X : Type u} {Y : Type v} (T : Teacher X Y)
    (C : ConceptClass X Y) : Prop :=
  T.target ∈ C ∧
  ∃ (k : ℕ),
    -- T's teaching sequence of length k uniquely identifies the target in C
    (∀ c ∈ C, c ≠ T.target →
      ∃ p ∈ T.teachingSequence k, c p.1 ≠ T.target p.1) ∧
    -- k is minimal: no teacher for the same target identifies it in fewer steps
    (∀ (T' : Teacher X Y), T'.target = T.target →
      (∀ c ∈ C, c ≠ T'.target →
        ∃ p ∈ T'.teachingSequence k, c p.1 ≠ T'.target p.1) →
      ∀ (k' : ℕ), k' < k →
        ∃ c ∈ C, c ≠ T'.target ∧
          ∀ p ∈ T'.teachingSequence k', c p.1 = T'.target p.1)
def IsAdversarial {X : Type u} {Y : Type v} (T : Teacher X Y)
    (C : ConceptClass X Y) : Prop :=
  T.target ∈ C ∧
  -- The teaching strategy maximizes the number of concepts in C
  -- consistent with data shown so far (maximally ambiguous examples)
  ∀ (data : List (X × Y)),
    ∀ (x' : X) (y' : Y),
      (Set.ncard { c ∈ C | ∀ p ∈ data ++ [T.teach data], c p.1 = p.2 }
        ≥ Set.ncard { c ∈ C | ∀ p ∈ data ++ [(x', y')], c p.1 = p.2 })
def IsRandomTeacher {X : Type u} {Y : Type v} (T : Teacher X Y) : Prop :=
  -- Teaching strategy is history-independent: the choice at step n+1
  -- does not depend on the examples shown at steps 1..n
  ∀ (data₁ data₂ : List (X × Y)), T.teach data₁ = T.teach data₂
structure MinimallyAdequateTeacher (X : Type u) (Y : Type v) where
  /-- Membership oracle -/
  mq : MembershipOracle X Y
  /-- Equivalence oracle -/
  eq : EquivalenceOracle X Y
  /-- Both answer about the same target -/
  consistent : mq.target = eq.target
structure MetaLearner (X : Type u) (Y : Type v) where
  /-- Given a concept class, produce a learner for that class -/
  metaLearn : ConceptClass X Y → BatchLearner X Y
structure LLMCritic (X : Type u) (Y : Type v) extends Teacher X Y where
  /-- Critique quality score -/
  critiqueQuality : ℝ
def Synthesizer (X : Type u) (Y : Type v) := List (X × Y) → Concept X Y
def Verifier (X : Type u) (Y : Type v) (spec : Concept X Y) :=
  fun (candidate : Concept X Y) => Option { x : X // candidate x ≠ spec x }


