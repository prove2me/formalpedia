-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PACBayes
-- name    : LeanPool_FormalLearningTheory_Theorem_PACBayes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:34:44.412307+00:00
-- url     : https://prove2.me/theorems/04c4a683-276e-4254-8dac-52ba8f1d892d
-- title:
--   PACBayes
-- statement:
--   Definitions and structural lemmas for PACBayes, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PACBayes.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open MeasureTheory Finset
noncomputable def gibbsError {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (Q : FinitePMF H) (hs : H → Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) : ℝ :=
  expectFinitePMF Q (fun h => TrueErrorReal X (hs h) c D)
noncomputable def gibbsEmpError {X : Type u}
    {H : Type*} [Fintype H]
    (Q : FinitePMF H) (hs : H → Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (S : Fin m → X) : ℝ :=
  expectFinitePMF Q (fun h =>
    EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool))


