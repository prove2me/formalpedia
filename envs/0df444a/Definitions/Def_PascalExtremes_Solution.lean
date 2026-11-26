-- Prove2me | Definitions.Def_PascalExtremes_Solution
-- name    : PascalExtremes_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:11:46.950156+00:00
-- url     : https://prove2.me/theorems/29706089-dfa5-47d3-be83-f61a30c5bb4f
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Upstream contributors (jfairfaxball-348/Pascal-Extremes; adapted in part under Apache-2.0 from jfairfaxball-348/pascal-minus-one; see pinned LICENSE and README.md)'s pinned Pascal Extremes: sharp prime-power divisibility and least extremal rows for restricted binomial gcds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/Solution.lean

module
public import Definitions.Def_PascalExtremes
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PascalExtremesPalomar
def admissibleIndices (N m : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k ↦ 0 < k ∧ m ∣ k
def G (N m : ℕ) : ℕ :=
  (admissibleIndices N m).gcd fun k ↦ N.choose k
def AdmissibleRow (m N : ℕ) : Prop :=
  m < N ∧ m ∣ N
def rP (p m : ℕ) : ℕ :=
  Nat.log p m + 1
def extremalRows (p m : ℕ) : Set ℕ :=
  {N | AdmissibleRow m N ∧
    padicValNat p (G N m) = rP p m}
noncomputable def T (p m : ℕ) : ℕ :=
  sInf (extremalRows p m)
end PascalExtremesPalomar


