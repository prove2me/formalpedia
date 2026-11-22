-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
-- name    : LeanPool_FormalLearningTheory_PureMath_KLDivergence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:24.921777+00:00
-- url     : https://prove2.me/theorems/32b21910-4ea1-47d2-83cd-8051c4ce1dd9
-- title:
--   KLDivergence
-- statement:
--   Definitions and structural lemmas for KLDivergence, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/KLDivergence.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
structure FinitePMF (H : Type*) [Fintype H] where
  /-- Probability assigned to each point. -/
  prob : H → ℝ
  prob_nonneg : ∀ h, 0 ≤ prob h
  prob_sum_one : ∑ h : H, prob h = 1
noncomputable def klDivFinitePMF {H : Type*} [Fintype H]
    (Q P : FinitePMF H) : ℝ :=
  ∑ h : H, if Q.prob h = 0 then 0
    else Q.prob h * Real.log (Q.prob h / P.prob h)
noncomputable def crossEntropyFinitePMF {H : Type*} [Fintype H]
    (Q P : FinitePMF H) : ℝ :=
  ∑ h : H, if Q.prob h = 0 then 0
    else Q.prob h * Real.log (1 / P.prob h)
noncomputable def expectFinitePMF {H : Type*} [Fintype H]
    (Q : FinitePMF H) (f : H → ℝ) : ℝ :=
  ∑ h : H, Q.prob h * f h
class HasPositivePrior {H : Type*} [Fintype H] (P : FinitePMF H) : Prop where
  pos : ∀ h, 0 < P.prob h


