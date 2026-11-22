-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation
-- name    : LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:35:40.187283+00:00
-- url     : https://prove2.me/theorems/12b000cf-5e5e-40e9-b9f6-b602a5d527b4
-- title:
--   Borel Analytic Separation
-- statement:
--   Definitions and structural lemmas for Borel Analytic Separation, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
noncomputable def zeroConcept : Concept ℝ Bool := fun _ => false
noncomputable def singletonConcept (a : ℝ) : Concept ℝ Bool :=
  fun x => if x = a then true else false
def singletonClassOn (A : Set ℝ) : ConceptClass ℝ Bool :=
  {h | h = zeroConcept ∨ ∃ a ∈ A, h = singletonConcept a}
def planarWitnessEvent (A : Set ℝ) : Set (ℝ × ℝ) :=
  {q | q.2 ∈ A ∧ q.1 ≠ q.2}
abbrev GhostPairs1 := (Fin 1 → ℝ) × (Fin 1 → ℝ)
def samplePair1ToPlane : GhostPairs1 → ℝ × ℝ :=
  fun p => (p.1 0, p.2 0)
def singletonBadEvent (A : Set ℝ) : Set GhostPairs1 :=
  {p | ∃ h ∈ singletonClassOn A,
    EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i))) (zeroOneLoss Bool) -
    EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i))) (zeroOneLoss Bool) ≥
      (1 : ℝ) / 2}


