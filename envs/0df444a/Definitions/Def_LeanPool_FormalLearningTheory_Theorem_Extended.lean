-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Extended
-- name    : LeanPool_FormalLearningTheory_Theorem_Extended
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:34:30.614691+00:00
-- url     : https://prove2.me/theorems/d4cd943f-c3d7-452c-bec7-8b00addcde2e
-- title:
--   Extended
-- statement:
--   Definitions and structural lemmas for Extended, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Extended.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Order.Group.Lattice
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
structure TaskEnvironment (X : Type u) where
  /-- Number of training tasks -/
  numTasks : ℕ
  /-- The concept classes for each task -/
  tasks : Fin numTasks → ConceptClass X Bool
structure MetaLearnerPAC (X : Type u) [MeasurableSpace X] where
  /-- Given training tasks, produce a learner for new tasks -/
  learn : TaskEnvironment X → BatchLearner X Bool
  /-- Given training tasks, produce a sample complexity function -/
  sampleComplexity : TaskEnvironment X → ℝ → ℝ → ℕ
structure TaskSampleEnvironment (X : Type u) [MeasurableSpace X] where
  /-- Number of training tasks -/
  numTasks : ℕ
  /-- Samples per task -/
  samplesPerTask : ℕ
  /-- The concept classes (one per task) -/
  taskClasses : Fin numTasks → ConceptClass X Bool
  /-- The true concepts (one per task, each in its class) -/
  trueConcepts : (j : Fin numTasks) → Concept X Bool
  /-- Each true concept is in its class -/
  concept_mem : ∀ j, trueConcepts j ∈ taskClasses j
structure SampleMetaLearner (X : Type u) [MeasurableSpace X] where
  /-- Given n × m labeled samples, produce a learner -/
  learn : {n m : ℕ} → (Fin n → Fin m → X × Bool) → BatchLearner X Bool
  /-- Given n × m, produce sample complexity for the new task -/
  sampleComplexity : ℕ → ℕ → ℝ → ℝ → ℕ
def AdviceEvalMeasurable
    {X : Type u} [MeasurableSpace X] {A : Type*}
    (LA : LearnerWithAdvice X Bool A) : Prop :=
  ∀ (a : A) (m : ℕ),
    Measurable (fun p : (Fin m → X × Bool) × X => LA.learnWithAdvice a p.1 p.2)
def PACLearnableWithAdviceRegular
    (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (A : Type*) [Fintype A] [nonemptyA : Nonempty A] : Prop :=
  Fintype.card A = Fintype.card A ∧ Classical.choice nonemptyA = Classical.choice nonemptyA ∧
  ∃ (LA : LearnerWithAdvice X Bool A) (mf_adv : ℝ → ℝ → ℕ),
    AdviceEvalMeasurable LA ∧
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∃ a : A,
          MeasureTheory.Measure.pi (fun _ : Fin (mf_adv ε δ) => D)
            {xs : Fin (mf_adv ε δ) → X |
              TrueError X (LA.learnWithAdvice a (fun i => (xs i, c (xs i)))) c D
                ≤ ENNReal.ofReal ε}
          ≥ ENNReal.ofReal (1 - δ)
def adviceTrainSample {X : Type u} {m₁ m₂ : ℕ}
    (S : Fin (m₁ + m₂) → X × Bool) : Fin m₁ → X × Bool :=
  fun i => S ⟨i.1, Nat.lt_add_right m₂ i.2⟩
def adviceValSample {X : Type u} {m₁ m₂ : ℕ}
    (S : Fin (m₁ + m₂) → X × Bool) : Fin m₂ → X × Bool :=
  fun j => S ⟨m₁ + j.1, Nat.add_lt_add_left j.2 m₁⟩
noncomputable def bestAdvice {X : Type u}
    {A : Type*} [Fintype A] [Nonempty A]
    (cand : A → Concept X Bool) {m : ℕ} (Sval : Fin m → X × Bool) : A :=
  Classical.choose <|
    Finset.exists_min_image Finset.univ
      (fun a => EmpiricalError X Bool (cand a) Sval (zeroOneLoss Bool))
      Finset.univ_nonempty
noncomputable def adviceSelectedHypothesis {X : Type u}
    {A : Type*} [Fintype A] [Nonempty A]
    (LA : LearnerWithAdvice X Bool A) {m₁ m₂ : ℕ}
    (S : Fin (m₁ + m₂) → X × Bool) : Concept X Bool :=
  let cand := fun a => LA.learnWithAdvice a (adviceTrainSample S)
  cand (bestAdvice cand (adviceValSample S))
def usedPrefix {X : Type u}
    (m₁ m₂ : ℕ) (xs : Fin (Nat.pair m₁ m₂) → X) : Fin (m₁ + m₂) → X :=
  fun i => xs (Fin.castLE (Nat.add_le_pair m₁ m₂) i)
def splitUsedEquiv {X : Type u} [MeasurableSpace X]
    (m₁ m₂ : ℕ) :
    (Fin (m₁ + m₂) → X) ≃ᵐ ((Fin m₁ → X) × (Fin m₂ → X)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin m₁ ⊕ Fin m₂ => X) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m₁ ⊕ Fin m₂ => X))


