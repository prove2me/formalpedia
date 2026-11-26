-- Prove2me | Definitions.Def_Erdos338_Pairs
-- name    : Erdos338_Pairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:58:14.010304+00:00
-- url     : https://prove2.me/theorems/bd297d57-7424-5ef6-a040-6ac000496a96
-- title:
--   Pairs
-- statement:
--   Definitions and structural lemmas for Pairs, from Veljko Janoski (veljjanoski/erdos338-palomar; includes Kneser's theorem adapted under Apache-2.0 from Mantas Baksys and Yael Dillies in YaelDillies/misc-yd and definitions under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 338: restricted order of robust sets of positive lower density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean

module
public import Definitions.Def_Erdos338_Structure
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace Erdos338Proof
open Classical in
/-- The `a ≤ m` with `a ∈ A`, `m - a ∈ A` and `2 a ≠ m`: the ordered representations of `m` as a
sum of two distinct elements of `A`. -/
noncomputable def rep (A : Set ℕ) (m : ℕ) : Finset ℕ :=
  (range (m + 1)).filter fun a ↦ a ∈ A ∧ m - a ∈ A ∧ 2 * a ≠ m
end Erdos338Proof


