-- Prove2me | Definitions.Def_Submission_ThreeSum_Radix
-- name    : Submission_ThreeSum_Radix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:27.687643+00:00
-- url     : https://prove2.me/theorems/3a6d5a26-c4aa-422f-8f32-4b31fd0f7e6b
-- title:
--   Radix
-- statement:
--   Definitions and structural lemmas for Radix, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Radix.lean

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Aesop
set_option autoImplicit false
namespace ThreeSum.Radix
open Finset
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
def localFiber (p : ℤ) (left right : Ω → ℤ) (a b : ℤ) : Finset Ω :=
  univ.filter fun ω => p ∣ a - left ω ∧ p ∣ b - right ω
def positionalHash (p : ℤ) (raw : Ω → ℤ) : List Ω → ℤ
  | [] => 0
  | ω :: rest => raw ω + p * positionalHash p raw rest
def representations (p : ℤ) (left right : Ω → ℤ) : ℕ → ℤ → ℤ → Finset (List Ω)
  | 0, _, _ => {[]}
  | j + 1, a, b =>
    (localFiber p left right a b).biUnion fun ω =>
      (representations p left right j ((a - left ω) / p) ((b - right ω) / p)).image
        (List.cons ω)
end ThreeSum.Radix


