-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Gold
-- name    : LeanPool_FormalLearningTheory_Criterion_Gold
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:20.491831+00:00
-- url     : https://prove2.me/theorems/9ac9d8b1-d22b-4bdd-a552-1cdd15d7af44
-- title:
--   Gold
-- statement:
--   Definitions and structural lemmas for Gold, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Criterion/Gold.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
def dataUpTo {X : Type u} {Y : Type v} (T : DataStream X Y) (t : ℕ) : List (X × Y) :=
  (List.range (t + 1)).map T.observe
def EXLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          L.conjecture (dataUpTo T.toDataStream t) = c
def BCLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          ∀ (x : X), (L.conjecture (dataUpTo T.toDataStream t)) x = c x
def FiniteLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          L.conjecture (dataUpTo T.toDataStream t) = c
          ∧ ∀ (t' : ℕ), t' ≥ t₀ →
              L.conjecture (dataUpTo T.toDataStream t') =
              L.conjecture (dataUpTo T.toDataStream t₀)
def VacillatoryLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (S : Finset (Concept X Bool)),
          (∀ h ∈ S, ∀ x, h x = c x) ∧
          ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
            L.conjecture (dataUpTo T.toDataStream t) ∈ S
def AnomalousLearnable (X : Type u) [Fintype X] (C : ConceptClass X Bool) (a : ℕ) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          Finset.card (Finset.filter
            (fun x => (L.conjecture (dataUpTo T.toDataStream t)) x ≠ c x)
            Finset.univ) ≤ a
def MonotonicLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    (∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          L.conjecture (dataUpTo T.toDataStream t) = c) ∧
    (∀ (data : List (X × Bool)) (xy : X × Bool),
      ∀ (x : X), (L.conjecture data) x = true →
        (L.conjecture (data ++ [xy])) x = true)
def TrialAndErrorLearnable (X : Type u) (C : ConceptClass X Bool) : Prop :=
  ∃ (L : GoldLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (T : TextPresentation X c),
        ∀ (x : X), ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          (L.conjecture (dataUpTo T.toDataStream t)) x = c x


