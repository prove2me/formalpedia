-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
-- name    : LeanPool_FormalLearningTheory_Complexity_Symmetrization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:34:06.66366+00:00
-- url     : https://prove2.me/theorems/d7e5a360-5904-48e5-adb7-7bdbec0f1994
-- title:
--   Symmetrization
-- statement:
--   Definitions and structural lemmas for Symmetrization, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
open MeasureTheory ENNReal
def WellBehavedVC (X : Type u) [MeasurableSpace X] (C : ConceptClass X Bool) : Prop :=
  ∀ (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (m : ℕ) (ε : ℝ),
    MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))


