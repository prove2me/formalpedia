-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Amalgamation
-- name    : LeanPool_FormalLearningTheory_Complexity_Amalgamation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:36:12.047582+00:00
-- url     : https://prove2.me/theorems/c2193970-4536-4f0b-9ddb-cd3eb62c10f5
-- title:
--   Amalgamation
-- statement:
--   Definitions and structural lemmas for Amalgamation, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Amalgamation.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open MeasureTheory
def agreementRel {Θ₁ Θ₂ S : Type*}
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S) : Set (Θ₁ × Θ₂) :=
  {p | π₁ p.1 = π₂ p.2}
def relParamClass {X : Type u}
    {Θ : Type*} (R : Set Θ) (e : Θ → Concept X Bool) : ConceptClass X Bool :=
  {h | ∃ θ ∈ R, h = e θ}
def amalgClass {X : Type u}
    {Θ₁ Θ₂ S : Type*}
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S)
    (merge : Θ₁ × Θ₂ → Concept X Bool) : ConceptClass X Bool :=
  relParamClass (agreementRel π₁ π₂) merge


