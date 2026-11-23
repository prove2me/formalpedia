-- Prove2me | solution 1 for Apportionmentlib.Election.n_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:41:25.569806+00:00
-- url     : https://prove2.me/submissions/a33bf992-81b4-4990-9b4d-30023bed6d37

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Rat.Floor
public import Definitions.Def_Apportionmentlib_Utils
public import Definitions.Def_Apportionmentlib_Basic

set_option autoImplicit false
@[expose] public section
public section
open BigOperators
open Apportionmentlib
namespace Apportionmentlib
namespace Election
theorem _root_.solution {n : ℕ} (election : Election n) : 0 < n := by
  have : n ≠ 0 := by
    by_contra hn
    rw [hn] at election
    simpa [Vector.eq_empty] using election.votes_sum_pos
  exact Nat.pos_of_ne_zero this
end Election
end Apportionmentlib
