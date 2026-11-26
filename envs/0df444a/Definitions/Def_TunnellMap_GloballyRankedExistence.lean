-- Prove2me | Definitions.Def_TunnellMap_GloballyRankedExistence
-- name    : TunnellMap_GloballyRankedExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:38:17.701048+00:00
-- url     : https://prove2.me/theorems/42332748-b95c-5aa2-a927-ec671e090976
-- title:
--   Globally Ranked Existence
-- statement:
--   Definitions and structural lemmas for Globally Ranked Existence, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRankedExistence.lean

import Definitions.Def_TunnellMap_GloballyRanked
set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*}
noncomputable def insertEquiv [DecidableEq S] [DecidableEq T]
    (s₀ : S) (t₀ : T) (M' : {s // s ≠ s₀} ≃ {t // t ≠ t₀}) : S ≃ T where
  toFun s := if hs : s = s₀ then t₀ else M' ⟨s, hs⟩
  invFun t := if ht : t = t₀ then s₀ else (M'.symm ⟨t, ht⟩).1
  left_inv := by
    intro s
    by_cases hs : s = s₀
    · subst s
      simp
    · have ht : (M' ⟨s, hs⟩ : T) ≠ t₀ := (M' ⟨s, hs⟩).2
      simp [hs, ht]
  right_inv := by
    intro t
    by_cases ht : t = t₀
    · subst t
      simp
    · have hs : ((M'.symm ⟨t, ht⟩ : {s // s ≠ s₀}) : S) ≠ s₀ :=
        (M'.symm ⟨t, ht⟩).2
      simp [ht, hs]
end GloballyRanked
end TunnellMap


