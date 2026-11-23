-- Prove2me | Definitions.Def_DeletedPrimes_Smooth
-- name    : DeletedPrimes_Smooth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:45:49.803227+00:00
-- url     : https://prove2.me/theorems/ba784728-5eab-44be-87b1-10a5e6bc93aa
-- title:
--   Smooth
-- statement:
--   Definitions and structural lemmas for Smooth, from BingoBaggins/deleted-primes contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Deleted-prime sets: composite window rigidity and exponent arithmetic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean

import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology
namespace DeletedPrimes
noncomputable section
open Classical
def liAlpha (α x : ℝ) : ℝ := ∫ u in (2 : ℝ)..x, u ^ (α - 1) / Real.log u
def piS (S : Set ℕ) (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter (· ∈ S)).card
def intervalCount (S : Set ℕ) (X : ℝ) : ℕ := ((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (· ∈ S)).card
end
end DeletedPrimes


