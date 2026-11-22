-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
-- name    : LeanPool_FormalLearningTheory_Complexity_Generalization_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:33:12.042914+00:00
-- url     : https://prove2.me/theorems/84e7a63a-2bb7-41e0-8030-3c5c4157b64f
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
noncomputable def SampleComplexity (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : ℝ → ℝ → ℕ :=
  fun ε δ => sInf { m : ℕ | ∃ (L : BatchLearner X Bool),
    ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ) }
noncomputable def QueryComplexity (X : Type u)
    (C : ConceptClass X Bool) : ℕ :=
  sInf { _q : ℕ | ∃ (L : ActiveLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (mq : MembershipOracle X Bool), mq.target = c →
        L.learnMQ mq = c }
noncomputable def LabelComplexity (X : Type u)
    (C : ConceptClass X Bool) : ℝ → ℝ → ℕ :=
  fun ε δ => sInf { _k : ℕ | ε = ε ∧ δ = δ ∧ ∃ (L : ActiveLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (mq : MembershipOracle X Bool), mq.target = c →
        L.learnMQ mq = c }
noncomputable def OptimalMistakeBound (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨅ (M : ℕ) (_ : MistakeBounded X Bool C M), (M : WithTop ℕ)
noncomputable def GeneralizationError (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (h : Concept X Y) (D : MeasureTheory.Measure (X × Y))
    (loss : LossFunction Y) : ℝ :=
  ∫ p, loss (h p.1) p.2 ∂D
noncomputable def EmpiricalError (X : Type u) (Y : Type v)
    (h : Concept X Y) {m : ℕ} (S : Fin m → X × Y)
    (loss : LossFunction Y) : ℝ :=
  if m = 0 then 0
  else (Finset.univ.sum fun i => loss (h (S i).1) (S i).2) / m
section ERM_section
open Classical in
/-- Empirical risk minimizer over a nonempty hypothesis space. -/
noncomputable def ermLearn (X : Type u) (Y : Type v)
    (H : HypothesisSpace X Y) (loss : LossFunction Y) (hne : H.Nonempty)
    {m : ℕ} (S : Fin m → X × Y) : Concept X Y :=
  if h : ∃ h₀ ∈ H, ∀ h' ∈ H,
      EmpiricalError X Y h₀ S loss ≤ EmpiricalError X Y h' S loss
  then h.choose
  else hne.some
theorem ermLearn_in_H (X : Type u) (Y : Type v)
    (H : HypothesisSpace X Y) (loss : LossFunction Y) (hne : H.Nonempty)
    {m : ℕ} (S : Fin m → X × Y) : ermLearn X Y H loss hne S ∈ H := by
  unfold ermLearn
  split
  · next h => exact h.choose_spec.1
  · exact hne.some_mem
noncomputable def ERM (X : Type u) (Y : Type v)
    (H : HypothesisSpace X Y) (loss : LossFunction Y)
    (hne : H.Nonempty) : BatchLearner X Y where
  hypotheses := H
  learn := fun {_m} S => ermLearn X Y H loss hne S
  output_in_H := fun S => ermLearn_in_H X Y H loss hne S
end ERM_section
section TrueError
noncomputable def TrueError (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) : ENNReal :=
  D { x | h x ≠ c x }
noncomputable def TrueErrorReal (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) : ℝ :=
  (TrueError X h c D).toReal
end TrueError
section EmpiricalMeasureError
noncomputable def EmpiricalMeasure (X : Type u) [MeasurableSpace X]
    {m : ℕ} (xs : Fin m → X) : MeasureTheory.Measure X :=
  if _hm : m = 0 then 0
  else (1 / m : ENNReal) • ∑ i : Fin m, MeasureTheory.Measure.dirac (xs i)
noncomputable def EmpiricalMeasureError (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (xs : Fin m → X) : ENNReal :=
  TrueError X h c (EmpiricalMeasure X xs)
end EmpiricalMeasureError
section Consistency
def IsConsistentWith (X : Type u) (Y : Type v)
    (h : Concept X Y) {m : ℕ} (S : Fin m → X × Y) : Prop :=
  ∀ i : Fin m, h (S i).1 = (S i).2
structure IsFaithfulLoss {Y : Type v} [DecidableEq Y] (loss : LossFunction Y) : Prop where
  /-- Matching predictions have zero loss -/
  loss_self_zero : ∀ y : Y, loss y y = 0
  /-- Zero loss implies matching predictions -/
  loss_zero_imp_eq : ∀ y₁ y₂ : Y, loss y₁ y₂ = 0 → y₁ = y₂
end Consistency
section ConcentrationInfrastructure
def HasBoundedDifferences {X : Type u} {m : ℕ} (f : (Fin m → X) → ℝ) (c : ℝ) : Prop :=
  ∀ (xs : Fin m → X) (i : Fin m) (x' : X),
    |f xs - f (Function.update xs i x')| ≤ c
end ConcentrationInfrastructure
section UniformConvergence
def HasUniformConvergence (X : Type u) [MeasurableSpace X]
    (H : HypothesisSpace X Bool) : Prop :=
  ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
    ∃ (m₀ : ℕ), ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), ∀ (m : ℕ), m₀ ≤ m →
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              ∀ (h : Concept X Bool), h ∈ H →
                |TrueErrorReal X h c D -
                 EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
                   (zeroOneLoss Bool)| < ε }
            ≥ ENNReal.ofReal (1 - δ)
structure QuantitativeUC (X : Type u) [MeasurableSpace X]
    (H : HypothesisSpace X Bool) where
  /-- Sample complexity function -/
  sampleBound : ℝ → ℝ → ℕ
  /-- The bound works: m ≥ sampleBound ε δ implies uniform convergence at (ε, δ) -/
  bound_works : ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
    ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), ∀ (m : ℕ), sampleBound ε δ ≤ m →
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            ∀ (h : Concept X Bool), h ∈ H →
              |TrueErrorReal X h c D -
               EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
                 (zeroOneLoss Bool)| < ε }
          ≥ ENNReal.ofReal (1 - δ)
end UniformConvergence
section ConcentrationBridge
noncomputable def PACsampleComplexity (d : ℕ) (ε δ : ℝ) : ℕ :=
  Nat.ceil ((8 / ε) * (d * Real.log (2 / ε) + Real.log (2 / δ)))
end ConcentrationBridge
noncomputable def Regret (X : Type u) (Y : Type v)
    (L : OnlineLearner X Y) (H : HypothesisSpace X Y)
    (seq : ℕ → X × Y) (T : ℕ) (loss : LossFunction Y) : ℝ :=
  let cumulLoss := L.cumulativeLoss loss ((List.range T).map seq)
  let seqList := (List.range T).map seq
  let bestFixed := sInf ((fun h => fixedHypothesisLoss h loss seqList) '' H)
  cumulLoss - bestFixed
section NFLCounting
end NFLCounting
section NFLInfrastructure
noncomputable def uniformMeasure (X : Type u) [MeasurableSpace X] [Fintype X]
    (hne : Nonempty X) : MeasureTheory.Measure X :=
  let _nonemptyWitness := hne
  (1 / (Fintype.card X : ENNReal)) • MeasureTheory.Measure.count
end NFLInfrastructure


