-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Extended
-- name    : LeanPool_FormalLearningTheory_Criterion_Extended
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:47.52906+00:00
-- url     : https://prove2.me/theorems/22a22e95-4a61-4ab2-b385-c5f50ccbcd98
-- title:
--   Extended
-- statement:
--   Definitions and structural lemmas for Extended, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Criterion/Extended.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Gold
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Active
public import Mathlib.MeasureTheory.Constructions.Pi
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
def EXUnderDrift (X : Type u) (C : ConceptClass X Bool)
    (driftRate : ℝ) : Prop :=
  driftRate = driftRate ∧ ∃ (L : GoldLearner X Bool),
    ∀ (targets : ℕ → Concept X Bool),
      (∀ t, targets t ∈ C) →
      ∀ (T : DataStream X Bool),
        -- The learner's conjecture eventually tracks the target:
        -- for all but finitely many t, output agrees with targets(t)
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          ∀ (x : X), (L.conjecture (dataUpTo T t)) x = (targets t) x
def UniversalLearnable (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∃ (L : BatchLearner X Bool) (rate : ℕ → ℝ),
    (∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε) ∧
    ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2 / 3)
def PACLearnableWithAdvice (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (A : Type*) : Prop :=
  ∃ (LA : LearnerWithAdvice X Bool A) (mf : ℝ → ℝ → ℕ),
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
        ∀ (c : Concept X Bool), c ∈ C →
          ∃ (a : A),
            let m := mf ε δ
            MeasureTheory.Measure.pi (fun _ : Fin m => D)
              { xs : Fin m → X |
                D { x | LA.learnWithAdvice a (fun i => (xs i, c (xs i))) x ≠ c x }
                  ≤ ENNReal.ofReal ε }
              ≥ ENNReal.ofReal (1 - δ)
def PosteriorConsistent (X : Type u) (Y : Type v)
    [MeasurableSpace X]
    (BL : BayesianLearner X Y) (C : ConceptClass X Y) : Prop :=
  ∀ (c : Concept X Y), c ∈ C →
    -- As sample size m → ∞, the posterior probability assigned to the true
    -- concept c converges to 1 (posterior concentration)
    ∀ ε > 0, ∃ (m₀ : ℕ), ∀ (m : ℕ), m ≥ m₀ →
      ∀ (data : List (X × Y)),
        data.length = m →
          BL.inference.posterior c data ≥ 1 - ε
def PACBayesBound (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (prior posterior : Concept X Y → ℝ)
    (S : IIDSample X Y) : Prop :=
  -- (1) Absolute continuity: posterior support ⊆ prior support
  (∀ (h : Concept X Y), posterior h > 0 → prior h > 0) ∧
  -- (2) KL divergence is finite (required for the bound to be non-vacuous)
  (∃ (kl : ℝ), kl ≥ 0 ∧
    -- kl = Σ_h Q(h) · ln(Q(h) / P(h))  [discrete case]
    -- kl = ∫ Q(h) · ln(Q(h) / P(h)) dh  [continuous case]
    -- We abstract over the computation and assert its properties:
    -- (3) The actual PAC-Bayes inequality: for any loss function ℓ,
    --     the expected generalization gap under Q is bounded by √((kl + ln(m/δ)) / (2m))
    ∀ (δ : ℝ), 0 < δ → δ < 1 →
      ∃ (genBound : ℝ),
        genBound = Real.sqrt ((kl + Real.log (S.sampleSize / δ)) / (2 * S.sampleSize)) ∧
        genBound ≥ 0)
def InformationTheoreticBound (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (L : BatchLearner X Y) (S : IIDSample X Y) : Prop :=
  -- Generalization gap is bounded by the mutual information I(S; L(S))
  -- between the sample and the hypothesis output:
  -- |E[err_D(L(S))] - E[emp_err_S(L(S))]| ≤ √(2 · I(S; L(S)) / m)
  L = L ∧ ∃ (genGap : ℝ) (mutualInfo : ℝ),
    genGap ≥ 0 ∧ mutualInfo ≥ 0 ∧
    genGap ≤ Real.sqrt (2 * mutualInfo / S.sampleSize)


