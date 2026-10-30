-- Prove2me | Definitions.Def_FBMSP_DynamicProgram
-- name    : FBMSP_DynamicProgram
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T04:52:09.000244+00:00
-- url     : https://prove2.me/theorems/b2ab85b7-dcc5-416c-af1d-7753e86357f9
-- title:
--   Consecutive-block Bellman recurrence and oracle cost schedule
-- statement:
--   This bundle defines a finite maximum, the consecutive-block Bellman recurrence, and an inductive relation witnessing a partition and its score. Its first parameter counts additional slots beyond an initial block; a $K$-price problem uses $K-1$. Empty blocks are permitted and should have zero score in the pricing application.
--
--   The cost layer counts nonempty block-oracle queries, Bellman candidate evaluations in a bottom-up table, arbitrary declared oracle charges, and reconstruction steps. These counts describe a specified memoized evaluation schedule. They do not claim that naive recursive evaluation has quadratic cost or that arbitrary real-valued oracle operations have unit bit complexity.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Proof of Theorem 2, pp.43–44 (ec9–ec10), Eq. (EC.6).

import Mathlib

noncomputable section
open scoped BigOperators
namespace FBMSP

/-- A maximum over the integers 0,...,n. -/
def prefixMax (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | n + 1 => max (prefixMax f n) (f (n + 1))

/-- k additional block slots, hence k+1 slots in total, on [a,a+n). -/
def intervalDP (W : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, a, n => W a (a + n)
  | k + 1, a, n =>
      prefixMax (fun i => intervalDP W k a i + W (a + i) (a + n)) n

inductive IntervalValue (W : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ → Prop
  | one (a n : ℕ) : IntervalValue W 0 a n (W a (a + n))
  | append {k a n i : ℕ} {v : ℝ} (hi : i ≤ n)
      (hv : IntervalValue W k a i v) :
      IntervalValue W (k + 1) a n (v + W (a + i) (a + n))

/-- Nonempty interval queries, counted by right endpoint. -/
def blockOracleCalls : ℕ → ℕ
  | 0 => 0
  | n + 1 => blockOracleCalls n + (n + 1)

/-- Bottom-up table schedule: k extra layers, columns 0,...,n, i+1 cuts
at column i. This is not the cost of naive recursive evaluation. -/
def tableCandidateEvaluations (k n : ℕ) : ℕ := k * blockOracleCalls (n + 1)

/-- One query costs m including the price and attained value; a Bellman
candidate is one arithmetic/comparison unit. Empty intervals cost zero. -/
def tableWork (k n m : ℕ) : ℕ :=
  m * blockOracleCalls n + tableCandidateEvaluations k n

/-- Actual declared charges of the primitive price-and-value oracle,
enumerating each nonempty interval exactly once by its right endpoint. -/
def oracleCharges (charge : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => oracleCharges charge n + ∑ a ∈ Finset.range (n + 1), charge a (n + 1)

/-- Cost of the memoized schedule with K slots: oracle precomputation,
Bellman candidates for K-1 extra layers, and K backtracking steps. -/
def segmentationWork (charge : ℕ → ℕ → ℕ) (K n : ℕ) : ℕ :=
  oracleCharges charge n + tableCandidateEvaluations (K - 1) n + K

end FBMSP


