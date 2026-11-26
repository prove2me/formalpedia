-- Prove2me | Definitions.Def_TunnellMap_GloballyRanked
-- name    : TunnellMap_GloballyRanked
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:36:36.358885+00:00
-- url     : https://prove2.me/theorems/f0939389-c6bb-5e19-8995-d7217b3ed4fc
-- title:
--   Globally Ranked
-- statement:
--   Definitions and structural lemmas for Globally Ranked, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRanked.lean

import Mathlib
set_option autoImplicit true
namespace TunnellMap
structure GloballyRanked (K S T : Type*) where
  rank : S → T → K
  source_injective : ∀ s, Function.Injective (rank s)
  target_injective : ∀ t, Function.Injective (fun s => rank s t)
namespace GloballyRanked
variable {K S T : Type*}
def Blocks [LT K] (I : GloballyRanked K S T) (M : S ≃ T) (s : S) (t : T) : Prop :=
  I.rank s t < I.rank s (M s) ∧
    I.rank s t < I.rank (M.symm t) t
def Stable [LT K] (I : GloballyRanked K S T) (M : S ≃ T) : Prop :=
  ∀ s t, ¬ I.Blocks M s t
section Finite
variable [LinearOrder K] [Fintype S] [Fintype T]
def InMatchingSymmDiff (M N : S ≃ T) (e : S × T) : Prop :=
  (M e.1 = e.2 ∧ N e.1 ≠ e.2) ∨
    (N e.1 = e.2 ∧ M e.1 ≠ e.2)
noncomputable def matchingSymmDiff (M N : S ≃ T) : Finset (S × T) := by
  classical
  exact (Finset.univ.product Finset.univ).filter (InMatchingSymmDiff M N)
end Finite
end GloballyRanked
end TunnellMap


