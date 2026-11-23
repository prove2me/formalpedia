-- Prove2me | Definitions.Def_DeletedPrimes_GoodScales
-- name    : DeletedPrimes_GoodScales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:45:44.77242+00:00
-- url     : https://prove2.me/theorems/7aa097db-2b97-4c6f-8dd0-b8f5d3077f5c
-- title:
--   Good Scales
-- statement:
--   Definitions and structural lemmas for Good Scales, from BingoBaggins/deleted-primes contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Deleted-prime sets: composite window rigidity and exponent arithmetic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean

import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology
namespace DeletedPrimes
noncomputable section
open Classical
def blockCount (S : Set ℕ) (Y : ℕ) : ℕ := ((Finset.Ico Y (2 * Y)).filter (· ∈ S)).card
def primeCount (S : Set ℕ) (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter (· ∈ S)).card
def mertensSum (S : Set ℕ) (α x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (· ∈ S), Real.log p / (p : ℝ) ^ α
def MertensLaw (S : Set ℕ) (α m : ℝ) : Prop :=
  Tendsto (fun x => mertensSum S α x / Real.log x) atTop (𝓝 m)
end
end DeletedPrimes


