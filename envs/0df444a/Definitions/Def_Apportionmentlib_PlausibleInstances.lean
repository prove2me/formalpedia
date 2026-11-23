-- Prove2me | Definitions.Def_Apportionmentlib_PlausibleInstances
-- name    : Apportionmentlib_PlausibleInstances
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:44:06.651889+00:00
-- url     : https://prove2.me/theorems/9efde171-9a65-4826-97d9-53cc8582bc20
-- title:
--   Plausible Instances
-- statement:
--   Definitions and structural lemmas for Plausible Instances, from mdbrnowski/apportionmentlib contributors (see pinned LICENSE and source headers)'s pinned Balinski–Young apportionment impossibility development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/PlausibleInstances.lean

module
public meta import Plausible.Arbitrary
public meta import Mathlib.Testing.Plausible.Sampleable
public meta import Definitions.Def_Apportionmentlib_Basic
public import Plausible.Arbitrary
public import Mathlib.Testing.Plausible.Sampleable
public import Definitions.Def_Apportionmentlib_Basic
public import Theorems.Thm_Apportionmentlib_Election_n_pos
public import Theorems.Thm_sum_pos_iff_exists_pos

set_option autoImplicit false
@[expose] public section
public section
@[expose] section
open Plausible
namespace Apportionmentlib
meta instance instShrinkableVectorNat {n : ℕ} : Shrinkable (Vector ℕ n) where
  shrink v :=
    (List.finRange n).flatMap fun (i : Fin n) =>
      (Shrinkable.shrink v[i]).map fun v' => v.set i v'
meta instance {n : ℕ} : Shrinkable (Election n) where
  shrink e :=
    let shrunkVotes := Shrinkable.shrink e.votes
    let shrunkHouseSizes := Shrinkable.shrink e.houseSize
    -- shrink votes only, shrink houseSize only, or shrink both
    (shrunkVotes.filterMap fun v =>
      if h : 0 < v.sum then some ⟨v, e.houseSize, h⟩ else none) ++
    (shrunkHouseSizes.map fun h => ⟨e.votes, h, e.votes_sum_pos⟩) ++
    (shrunkVotes.flatMap fun v =>
      if hv : 0 < v.sum then shrunkHouseSizes.map fun h => ⟨v, h, hv⟩ else [])
meta instance {n : ℕ} [NeZero n] : Arbitrary (Election n) where
  arbitrary := do
    let votes ← (Vector.replicate n ()).mapM fun _ => Gen.chooseNat
    let houseSize ← Gen.choose Nat 1 20 (by decide)
    have n_pos := NeZero.pos n
    let votes' := votes.set 0 (votes[0] + 1)
    return {
      votes := votes',
      houseSize := ⟨houseSize.val, houseSize.prop.left⟩,
      votes_sum_pos := by
        rw [sum_pos_iff_exists_pos]
        exact ⟨0, by simp [votes']⟩
    }
meta instance {n : ℕ} [NeZero n] : SampleableExt (Election n) := SampleableExt.selfContained
end Apportionmentlib


