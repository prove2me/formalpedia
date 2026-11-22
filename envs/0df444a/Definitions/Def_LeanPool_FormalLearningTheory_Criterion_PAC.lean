-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
-- name    : LeanPool_FormalLearningTheory_Criterion_PAC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:45.838354+00:00
-- url     : https://prove2.me/theorems/2843c445-4f28-4487-8f2c-784286773bfd
-- title:
--   PAC
-- statement:
--   Definitions and structural lemmas for PAC, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Criterion/PAC.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Active
public import Mathlib.MeasureTheory.Constructions.Pi
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
def PACLearnable (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
        ∀ (c : Concept X Bool), c ∈ C →
          let m := mf ε δ
          -- D^m: the i.i.d. product measure on Fin m → X
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            -- The success event: error of L on labeled sample ≤ ε
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal ε }
            ≥ ENNReal.ofReal (1 - δ)
def AgnosticPACLearnable (X : Type u) [MeasurableSpace X]
    (H : HypothesisSpace X Bool) : Prop :=
  ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      ∀ (D : MeasureTheory.Measure (X × Bool)), MeasureTheory.IsProbabilityMeasure D →
        let m := mf ε δ
        -- D^m: the i.i.d. product measure on Fin m → X × Bool
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          -- Success event: learner is competitive with best h ∈ H
          { S : Fin m → X × Bool |
            ∀ (h : Concept X Bool), h ∈ H →
              D { p | L.learn S p.1 ≠ p.2 } ≤
                D { p | h p.1 ≠ p.2 } + ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ)
def ExactLearnable (X : Type u)
    (C : ConceptClass X Bool) : Prop :=
  ∃ (L : ActiveLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (mq : MembershipOracle X Bool),
        mq.target = c →
          L.learnMQ mq = c


