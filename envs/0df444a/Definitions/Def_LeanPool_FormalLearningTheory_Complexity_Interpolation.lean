-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
-- name    : LeanPool_FormalLearningTheory_Complexity_Interpolation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:35:47.694595+00:00
-- url     : https://prove2.me/theorems/c457f687-706a-4c32-97b3-ee6d13224c44
-- title:
--   Interpolation
-- statement:
--   Definitions and structural lemmas for Interpolation, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open MeasureTheory
attribute [local instance] Classical.propDecidable
noncomputable def piecewiseConcept {X : Type u}
    (A : Set X) (h₁ h₂ : Concept X Bool) : Concept X Bool :=
  fun x => if x ∈ A then h₁ x else h₂ x
noncomputable def routerOfSet {X : Type u}
    (A : Set X) : Unit → Concept X Bool :=
  fun u x => if u = () then if x ∈ A then true else false else false
noncomputable def routerOfSetFamily {X : Type u}
    (A : ℕ → Set X) : ℕ → Concept X Bool :=
  fun n x => if x ∈ A n then true else false
def interpClassFixed {X : Type u}
    (C₁ C₂ : ConceptClass X Bool) (A : Set X) : ConceptClass X Bool :=
  {h | ∃ h₁ ∈ C₁, ∃ h₂ ∈ C₂, h = piecewiseConcept A h₁ h₂}
def interpClassCountable {X : Type u}
    (C₁ C₂ : ConceptClass X Bool) (A : ℕ → Set X) : ConceptClass X Bool :=
  {h | ∃ n, ∃ h₁ ∈ C₁, ∃ h₂ ∈ C₂, h = piecewiseConcept (A n) h₁ h₂}
def interpClass {X : Type u} [MeasurableSpace X]
    (C₁ C₂ : ConceptClass X Bool) : ConceptClass X Bool :=
  {h | ∃ A : Set X, MeasurableSet A ∧ ∃ h₁ ∈ C₁, ∃ h₂ ∈ C₂,
    h = piecewiseConcept A h₁ h₂}
structure BorelRouterCode (X : Type u) [MeasurableSpace X] where
  /-- The router parameter space -/
  Ρ : Type u
  /-- MeasurableSpace instance on Ρ -/
  instMeasΡ : MeasurableSpace Ρ
  /-- StandardBorelSpace instance on Ρ -/
  instStdΡ : @StandardBorelSpace Ρ instMeasΡ
  /-- The router evaluation map -/
  eval : Ρ → Concept X Bool
  /-- Joint measurability of the evaluation map -/
  eval_meas : @Measurable (Ρ × X) Bool (instMeasΡ.prod ‹MeasurableSpace X›)
    (⊤ : MeasurableSpace Bool) (fun p => eval p.1 p.2)
def HasFullInterpolationRouterCode (X : Type u) [MeasurableSpace X] : Prop :=
  Nonempty (BorelRouterCode X)


