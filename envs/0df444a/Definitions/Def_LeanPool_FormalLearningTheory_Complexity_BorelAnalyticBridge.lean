-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
-- name    : LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:35:10.404715+00:00
-- url     : https://prove2.me/theorems/a16bb617-1b74-4b4c-8617-3c152cfad64e
-- title:
--   Borel Analytic Bridge
-- statement:
--   Definitions and structural lemmas for Borel Analytic Bridge, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open MeasureTheory
abbrev GhostPairs (X : Type u) (m : ℕ) := (Fin m → X) × (Fin m → X)
def paramWitnessSet
    {X : Type u}
    {Θ : Type*}
    (e : Θ → Concept X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ) :
    Set (Θ × GhostPairs X m) :=
  {q | EmpiricalError X Bool (e q.1) (fun i => (q.2.2 i, c (q.2.2 i))) (zeroOneLoss Bool) -
       EmpiricalError X Bool (e q.1) (fun i => (q.2.1 i, c (q.2.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
def paramBadEvent
    {X : Type u}
    {Θ : Type*}
    (e : Θ → Concept X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ) :
    Set (GhostPairs X m) :=
  Prod.snd '' paramWitnessSet e c m ε
def patchEval
    {X : Type u}
    {Θ₁ Θ₂ Ρ : Type*}
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool) :
    (Θ₁ × Θ₂ × Ρ) → Concept X Bool :=
  fun θ x => if r θ.2.2 x then e₁ θ.1 x else e₂ θ.2.1 x
noncomputable abbrev GhostPairMeasure
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) (m : ℕ) :
    MeasureTheory.Measure ((Fin m → X) × (Fin m → X)) :=
  (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
    (MeasureTheory.Measure.pi (fun _ : Fin m => D))


