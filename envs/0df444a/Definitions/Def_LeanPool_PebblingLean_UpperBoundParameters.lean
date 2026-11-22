-- Prove2me | Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
-- name    : LeanPool_PebblingLean_UpperBoundParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:54:56.647647+00:00
-- url     : https://prove2.me/theorems/98485817-caed-4f84-a20c-064b09f171dc
-- title:
--   Upper Bound Parameters
-- statement:
--   Definitions and structural lemmas for Upper Bound Parameters, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
namespace PaperParameters
noncomputable def splitM (K : ℝ) (n : ℕ) : ℕ :=
  ⌈K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))⌉₊
noncomputable def splitA (K : ℝ) (n : ℕ) : ℕ :=
  n - splitM K n
def minPile (n : ℕ) : ℕ :=
  2 ^ (n / 5)
noncomputable def loss (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 2)⁻¹
noncomputable def costMultiplier (K : ℝ) (n : ℕ) : ℕ :=
  ⌈(1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n)⌉₊
noncomputable def recursiveCostBound (K : ℝ) (n0 : ℕ) (n : ℕ) : ℕ :=
  if n < n0 then
    2 ^ n * minPile n
  else if h : splitM K n < n then
    recursiveCostBound K n0 (splitM K n) * costMultiplier K n
  else
    2 ^ n * minPile n
termination_by n
decreasing_by exact h
noncomputable def annulusWidth (A K : ℝ) (n : ℕ) : ℕ :=
  ⌈A * Real.sqrt ((splitA K n : ℝ) * Real.log (2 * (n : ℝ) ^ 2))⌉₊
noncomputable def annulusWidthCore (A K : ℝ) (n : ℕ) : ℝ :=
  A * Real.sqrt ((splitA K n : ℝ) * Real.log (2 * (n : ℝ) ^ 2))
noncomputable def rIn (A K : ℝ) (n : ℕ) : ℕ :=
  splitA K n / 3 - annulusWidth A K n
noncomputable def rOut (A K : ℝ) (n : ℕ) : ℕ :=
  splitA K n / 3 + annulusWidth A K n
noncomputable def sampleCountForDemand (A K : ℝ) (n t : ℕ) : ℕ :=
  ⌈((1 + loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n)) /
    (2 ^ rOut A K n : ℝ)⌉₊
noncomputable def demandGap (K : ℝ) (costBound : ℕ → ℕ) (n : ℕ) : ℝ :=
  loss n * (costBound (splitM K n) : ℝ) / 4
noncomputable def demandGapForDemand (n t : ℕ) : ℝ :=
  loss n * (t : ℝ) / 4
noncomputable def stackMargin : ℝ :=
  Real.log ((4 : ℝ) / 3) - Real.log 2 / 3
noncomputable def leftChernoffTerm (A K : ℝ) (lamLeft : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (lamLeft n * (rIn A K n : ℝ)) *
    (((1 : ℝ) / 3) * Real.exp (-(lamLeft n)) + ((2 : ℝ) / 3)) ^
      splitA K n
noncomputable def rightChernoffTerm (A K : ℝ) (lamRight : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(lamRight n * (rOut A K n : ℝ))) *
    (((1 : ℝ) / 3) * Real.exp (lamRight n) + ((2 : ℝ) / 3)) ^
      splitA K n
noncomputable def annulusChernoffLambda (A K : ℝ) (n : ℕ) : ℝ :=
  3 * (annulusWidth A K n : ℝ) / ((splitA K n : ℝ) + 1)
def explicitCutoff : ℕ :=
  36329454321664
end PaperParameters
end Hypercube
end PebblingLean


