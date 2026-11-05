-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:05:02.795277+00:00
-- url     : https://prove2.me/theorems/79ea638e-c3e5-40cd-aff2-9def2bc84694
-- title:
--   Cache
-- statement:
--   Definitions and structural lemmas for Cache, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
namespace WeightedCache
open Finset
abbrev Word (N : ℕ) := Fin N → Fin 3
def rank {N : ℕ} (R : Word N) : ℕ := ∑ i, (R i).val
def cost {N : ℕ} (c : Fin 3 → ℕ) (R : Word N) : ℕ := ∑ i, c (R i)
def Below {N : ℕ} (R Q : Word N) : Prop := ∀ i, R i ≤ Q i
instance {N : ℕ} (R Q : Word N) : Decidable (Below R Q) :=
  inferInstanceAs (Decidable (∀ i, R i ≤ Q i))
def bank (N : ℕ) (c : Fin 3 → ℕ) (T : ℕ) : Finset (Word N) :=
  univ.filter (fun R => cost c R ≤ T)
def deficit {N : ℕ} (c : Fin 3 → ℕ) (Q R : Word N) : ℕ :=
  ∑ i, (c (Q i) - c (R i))
def near {N : ℕ} (c : Fin 3 → ℕ) (Q : Word N) (D : ℕ) : Finset (Word N) :=
  univ.filter (fun R => Below R Q ∧ deficit c Q R ≤ D)
def digitWeight (c : Fin 3 → ℕ) (z : ℝ) (q r : Fin 3) : ℝ :=
  if r ≤ q then z ^ (c q - c r) else 0
def predecessor {N : ℕ} (R : Word N) (i : Fin N) : Word N :=
  Function.update R i ⟨(R i).val - 1, by omega⟩
def weight {N : ℕ} (R A : Word N) : ℤ := ∏ i, ((R i).val.choose (A i).val : ℤ)
def zeta {N : ℕ} (f : Word N → ℤ) (R : Word N) : ℤ := ∑ A, weight R A * f A
def recover {N : ℕ} (B : Finset (Word N)) (values : Word N → ℤ) (h : ℕ) :
    ℕ → Word N → ℤ
  | 0, R => values R
  | k + 1, R => if R ∈ B then values R else
      (∑ i : Fin N, (R i).val * recover B values h k (predecessor R i)) /
        ((rank R : ℤ) - (h : ℤ))
end WeightedCache
end WeightedCache3SUMRefinement_e1ae71d


