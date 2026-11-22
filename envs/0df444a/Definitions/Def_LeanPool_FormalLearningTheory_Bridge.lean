-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Bridge
-- name    : LeanPool_FormalLearningTheory_Bridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:33:37.114217+00:00
-- url     : https://prove2.me/theorems/9c0411ab-4618-407e-885e-cf65e380f4e3
-- title:
--   Bridge
-- statement:
--   Definitions and structural lemmas for Bridge, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
def conceptClassToSetFamily (X : Type u) (C : ConceptClass X Bool) : Set (Set X) :=
  { S | ∃ c ∈ C, S = { x | c x = true } }
noncomputable def setFamilyToConceptClass (X : Type u) (F : Set (Set X)) : ConceptClass X Bool :=
  { c : X → Bool | { x | c x = true } ∈ F }
def conceptToFinset {X : Type u} [Fintype X] (c : X → Bool) : Finset X :=
  Finset.univ.filter (fun x => c x = true)
def conceptClassToFinsetFamily {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) : Finset (Finset X) :=
  C.image conceptToFinset
def restrictToFinset {X : Type u} (c : X → Bool) (S : Finset X) : ↥S → Bool :=
  fun ⟨x, _⟩ => c x
def restrictConceptClass {X : Type u}
    (C : Finset (X → Bool)) (S : Finset X) : Finset (↥S → Bool) :=
  C.image (fun c => restrictToFinset c S)
def funcToSubsetFamily {X : Type u} [DecidableEq X] (S : Finset X)
    (fs : Finset (↥S → Bool)) : Finset (Finset ↥S) :=
  fs.image (fun f => Finset.univ.filter (fun x => f x = true))
def iidSampleToProbMeasure (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : IIDSample X Y) : MeasureTheory.Measure (X × Y) :=
  S.distribution
instance iidSampleIsProbability (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : IIDSample X Y) : MeasureTheory.IsProbabilityMeasure S.distribution :=
  S.isProbability
noncomputable def withTopNatToOrdinal : WithTop ℕ → Ordinal
  | some n => (n : Ordinal)
  | none => Ordinal.omega0
noncomputable def onlineToBatch (X : Type u) (Y : Type v)
    (OL : OnlineLearner X Y) : BatchLearner X Y where
  hypotheses := Set.univ -- online learner's implicit hypothesis space
  learn := fun {_m} S =>
    let finalState := (List.ofFn S).foldl (fun s p => OL.update s p.1 p.2) OL.init
    fun x => OL.predict finalState x
  output_in_H := fun _ => Set.mem_univ _
def bayesianToBatch (X : Type u) (Y : Type v) [MeasurableSpace X]
    (BL : BayesianLearner X Y) : BatchLearner X Y where
  hypotheses := BL.hypotheses
  learn := BL.learnMAP
  output_in_H := BL.output_in_H


