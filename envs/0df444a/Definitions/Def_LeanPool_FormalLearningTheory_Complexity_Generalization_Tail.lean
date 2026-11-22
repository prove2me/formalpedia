-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
-- name    : LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:33:33.327827+00:00
-- url     : https://prove2.me/theorems/9f5b3365-26ba-40ad-8084-2525da1926e0
-- title:
--   Tail
-- statement:
--   Definitions and structural lemmas for Tail, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
section FinBlockInfrastructure
open Equiv in
/-- Extract block j from a flat array of k*m elements, using finProdFinEquiv. -/
def blockExtract {α : Type*} (k m : ℕ) (S : Fin (k * m) → α) (j : Fin k) : Fin m → α :=
  fun i => S (finProdFinEquiv (j, i))
def majorityVote (k : ℕ) (votes : Fin k → Bool) : Bool :=
  decide (2 * (Finset.univ.filter (fun j => votes j = true)).card > k)
end FinBlockInfrastructure
section PACTheoremHelpers
end PACTheoremHelpers
abbrev DriftRate := ℝ


