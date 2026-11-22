-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
-- name    : LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:34:26.333852+00:00
-- url     : https://prove2.me/theorems/b4dd762b-ccc2-46f8-9847-49c80c540ca2
-- title:
--   Finite Support UC
-- statement:
--   Definitions and structural lemmas for Finite Support UC, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/FiniteSupportUC.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset MeasureTheory
noncomputable section
universe u
noncomputable def FinitePMF.toPMF {H : Type*} [Fintype H] (μ : FinitePMF H) : PMF H :=
  PMF.ofFintype (fun h => ENNReal.ofReal (μ.prob h)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun h _ => μ.prob_nonneg h)]
    simpa using congrArg ENNReal.ofReal μ.prob_sum_one)
def extendBool {H : Type*} (a : H → Bool) : H ⊕ ℕ → Bool
  | Sum.inl h => a h
  | Sum.inr _ => false
def liftClass {H : Type*} (A : Finset (H → Bool)) :
    ConceptClass (H ⊕ ℕ) Bool :=
  { h | ∃ a ∈ A, h = extendBool a }
end


