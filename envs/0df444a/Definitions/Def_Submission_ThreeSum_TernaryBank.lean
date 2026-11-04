-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryBank
-- name    : Submission_ThreeSum_TernaryBank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:31:37.883259+00:00
-- url     : https://prove2.me/theorems/612cca6d-1d2a-46ce-8b30-7c3b826af3ed
-- title:
--   Ternary Bank
-- statement:
--   Definitions and structural lemmas for Ternary Bank, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
def rank {N : ℕ} (R : TritWord N) : ℕ := ∑ i, (R i).val
def Below {N : ℕ} (R Q : TritWord N) : Prop := ∀ i, R i ≤ Q i
instance {N : ℕ} (R Q : TritWord N) : Decidable (Below R Q) :=
  inferInstanceAs (Decidable (∀ i, R i ≤ Q i))
def bank (N T : ℕ) : Finset (TritWord N) := univ.filter (fun R => rank R ≤ T)
def deficit {N : ℕ} (Q R : TritWord N) : ℕ := ∑ i, ((Q i).val - (R i).val)
def lowerWords {N : ℕ} (Q : TritWord N) : Finset (TritWord N) :=
  univ.filter (fun R => Below R Q)
def nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) : Finset (TritWord N) :=
  (lowerWords Q).filter (fun R => deficit Q R ≤ D)
def digitDeficitWeight (z : ℝ) (q r : Fin 3) : ℝ :=
  if r ≤ q then z ^ (q.val - r.val) else 0
end ThreeSum.TernaryBank


