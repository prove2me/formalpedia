-- Prove2me | Definitions.Def_Submission_ThreeSum_PrimeChain
-- name    : Submission_ThreeSum_PrimeChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:05.071892+00:00
-- url     : https://prove2.me/theorems/b34b7711-f13e-4462-9e04-578f37ecf148
-- title:
--   Prime Chain
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean

import Definitions.Def_Submission_ThreeSum_Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace ThreeSum.PrimeChain
open Finset
open scoped BigOperators
variable {ι : Type*}
def score (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (q : ℕ) : ℕ :=
  ∑ i ∈ T, if q ∣ (difference i).natAbs then weight (difference i) else 0
def selectPrime (candidates : List ℕ) (T : Finset ι) (difference : ι → ℤ)
    (weight : ℤ → ℕ) (q : ℕ) : ℕ :=
  (candidates.argmin fun p => score T difference weight (q * p)).getD 0
def modulus (candidates : List ℕ) (T : Finset ι) (difference : ι → ℤ)
    (weight : ℤ → ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 =>
    let q := modulus candidates T difference weight r
    q * selectPrime candidates T difference weight q
end ThreeSum.PrimeChain


