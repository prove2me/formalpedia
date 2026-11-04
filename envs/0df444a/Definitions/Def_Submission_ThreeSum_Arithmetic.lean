-- Prove2me | Definitions.Def_Submission_ThreeSum_Arithmetic
-- name    : Submission_ThreeSum_Arithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:33.624797+00:00
-- url     : https://prove2.me/theorems/8df38f3b-335a-441d-b47a-e746fb4035d4
-- title:
--   Arithmetic
-- statement:
--   Definitions and structural lemmas for Arithmetic, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace ThreeSum.Arithmetic
open Finset
open scoped BigOperators
def SmallLift (j : ℤ) : Prop := j = -1 ∨ j = 0 ∨ j = 1
def dividesIndicator (m x : ℤ) : ℕ := if m ∣ x then 1 else 0
def missWeight (L : Finset ℤ) (x : ℤ) : ℕ :=
  ∑ l ∈ L, if l ∣ x then 0 else 1
def modCount {ι : Type*} (T : Finset ι) (difference : ι → ℤ) (m : ℤ) : ℕ :=
  ∑ i ∈ T, dividesIndicator m (difference i)
def weightedFalseCount {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (m : ℤ) : ℕ :=
  ∑ i ∈ T, if m ∣ difference i then missWeight L (difference i) else 0
def fiberWeight {ι τ : Type*} [DecidableEq τ] (I : Finset ι)
    (owner : ι → τ) (weight : ι → ℕ) (t : τ) : ℕ :=
  ∑ i ∈ I, if owner i = t then weight i else 0
end ThreeSum.Arithmetic


