-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
-- name    : LeanPool_FormalLearningTheory_Complexity_Rademacher
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:33:36.223095+00:00
-- url     : https://prove2.me/theorems/bf55a7f1-3ccd-41b5-b844-4149b1daaef5
-- title:
--   Rademacher
-- statement:
--   Definitions and structural lemmas for Rademacher, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
noncomputable def boolToSign (b : Bool) : ℝ := if b then 1 else -1
abbrev SignVector (m : ℕ) := Fin m → Bool
def flipAt {m : ℕ} (i : Fin m) (σ : SignVector m) : SignVector m :=
  Function.update σ i (!σ i)
noncomputable def rademacherCorrelation {X : Type u} {m : ℕ}
    (h : Concept X Bool) (σ : SignVector m) (xs : Fin m → X) : ℝ :=
  if _hm : m = 0 then 0
  else (1 / (m : ℝ)) * ∑ i : Fin m, boolToSign (σ i) * boolToSign (h (xs i))
noncomputable def EmpiricalRademacherComplexity (X : Type u)
    (C : ConceptClass X Bool) {m : ℕ} (xs : Fin m → X) : ℝ :=
  if _hm : m = 0 then 0
  else
    let numSigns : ℝ := (Fintype.card (SignVector m) : ℝ)
    (1 / numSigns) * ∑ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs }
noncomputable def RademacherComplexity (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (m : ℕ) : ℝ :=
  ∫ xs : Fin m → X,
    EmpiricalRademacherComplexity X C xs
    ∂(MeasureTheory.Measure.pi (fun _ : Fin m => D))


