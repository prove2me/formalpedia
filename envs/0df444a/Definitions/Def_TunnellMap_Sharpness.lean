-- Prove2me | Definitions.Def_TunnellMap_Sharpness
-- name    : TunnellMap_Sharpness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:28:57.797337+00:00
-- url     : https://prove2.me/theorems/32bb6587-0443-511c-8350-12db7984c396
-- title:
--   Sharpness
-- statement:
--   Definitions and structural lemmas for Sharpness, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Sharpness.lean

import Definitions.Def_TunnellMap_ParkingRearrangement
set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
def sharpRank (m : ℕ) (s t : Fin m) : ℕ :=
  (m + 1) * s.1 + t.1
theorem sharpRank_source_injective (m : ℕ) (s : Fin m) :
    Function.Injective (sharpRank m s) := by
  intro t₁ t₂ h
  apply Fin.ext
  exact Nat.add_left_cancel h
theorem sharpRank_target_injective (m : ℕ) (t : Fin m) :
    Function.Injective (fun s => sharpRank m s t) := by
  intro s₁ s₂ h
  apply Fin.ext
  apply mul_left_cancel₀ (by omega : m + 1 ≠ 0)
  exact Nat.add_right_cancel h
def sharpRanking (m : ℕ) : GloballyRanked ℕ (Fin m) (Fin m) where
  rank := sharpRank m
  source_injective := sharpRank_source_injective m
  target_injective := sharpRank_target_injective m
def sharpMatching (m : ℕ) : Fin m ≃ Fin m := Equiv.refl (Fin m)
end GloballyRanked
end TunnellMap


