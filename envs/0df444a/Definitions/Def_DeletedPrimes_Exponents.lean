-- Prove2me | Definitions.Def_DeletedPrimes_Exponents
-- name    : DeletedPrimes_Exponents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:43:18.663316+00:00
-- url     : https://prove2.me/theorems/e65d98eb-3a31-497e-befe-e10d9e339fb7
-- title:
--   Exponents
-- statement:
--   Definitions and structural lemmas for Exponents, from BingoBaggins/deleted-primes contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Deleted-prime sets: composite window rigidity and exponent arithmetic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean

import Mathlib
set_option autoImplicit false
open Real Filter Topology
namespace DeletedPrimes
noncomputable section
def kappaOne (α : ℝ) : ℝ := (1 - α) / (1 + (1 - α) ^ 2)
def kappaK (k : ℕ) (α : ℝ) : ℝ :=
  if α ≤ 1 / 2 then (1 - α) / (2 * (1 - α) + α ^ 2 / k) else (1 - α) / (1 + (1 - α) ^ 2 / k)
def hitExp (k : ℕ) (α κ τ : ℝ) : ℝ :=
  (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
    fun i => α * κ * i / k + max (κ - τ - κ * i / k) 0
def errExp (k : ℕ) (α κ τ : ℝ) : ℝ := (α - 1) + κ + τ * (1 - α) + hitExp k α κ τ - α * κ
def maxExp (k : ℕ) (α κ : ℝ) : ℝ :=
  if α ≤ 1 / 2 then (α - 1) + κ * (2 - 2 * α + α ^ 2 / k) else (α - 1) + κ * (1 + (1 - α) ^ 2 / k)
def argmaxExp (k : ℕ) (α κ : ℝ) : ℝ := if α ≤ 1 / 2 then κ - α * κ / k else κ * (1 - α) / k
end
end DeletedPrimes


