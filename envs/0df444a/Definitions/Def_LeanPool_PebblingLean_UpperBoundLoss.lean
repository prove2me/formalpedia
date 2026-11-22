-- Prove2me | Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
-- name    : LeanPool_PebblingLean_UpperBoundLoss
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:54:29.092097+00:00
-- url     : https://prove2.me/theorems/fe01de41-6e28-4832-bc92-013ca11eb3da
-- title:
--   Upper Bound Loss
-- statement:
--   Definitions and structural lemmas for Upper Bound Loss, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
namespace LossRecurrence
def iterate (next : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => iterate next k (next n)
def ActiveFor (next : ℕ → ℕ) (n0 : ℕ) : ℕ → ℕ → Prop
  | 0, _n => True
  | k + 1, n => n0 ≤ n ∧ ActiveFor next n0 k (next n)
def lossProduct (next : ℕ → ℕ) (loss : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _n => 1
  | k + 1, n => (1 + loss n) * lossProduct next loss k (next n)
def lossSum (next : ℕ → ℕ) (loss : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _n => 0
  | k + 1, n => loss n + lossSum next loss k (next n)
def geomSum (q : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, q ^ i
end LossRecurrence
noncomputable def normalizedCost (costBound : ℕ → ℕ) (n : ℕ) : ℝ :=
  (costBound n : ℝ) / (((4 : ℝ) / 3) ^ n)
noncomputable def finiteBaseNormalizedBound (costBound : ℕ → ℕ) (n0 : ℕ) : ℝ :=
  ∑ n ∈ Finset.range n0, normalizedCost costBound n
def HasRealHypercubePebblingUpperBound (C : ℝ) : Prop :=
  ∀ n : ℕ, ∃ k : ℕ,
    Pebbling.HasSolvableAtMostSize (graph n) 1 k ∧
      (k : ℝ) ≤ C * (((4 : ℝ) / 3) ^ n)
end Hypercube
end PebblingLean


