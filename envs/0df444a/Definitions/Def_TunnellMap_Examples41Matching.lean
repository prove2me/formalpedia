-- Prove2me | Definitions.Def_TunnellMap_Examples41Matching
-- name    : TunnellMap_Examples41Matching
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:33:55.375004+00:00
-- url     : https://prove2.me/theorems/a68dd286-75e1-4490-a379-1326a4f0bf93
-- title:
--   Examples41 Matching
-- statement:
--   Definitions and structural lemmas for Examples41 Matching, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
set_option autoImplicit true
namespace TunnellMap
namespace Examples41
open GloballyRanked
set_option maxRecDepth 10000
def rank2 (s t : Fin 2) : ℕ := 2 * t.1 + s.1 + 1
def ranking2 : GloballyRanked ℕ (Fin 2) (Fin 2) where
  rank := rank2
  source_injective := by decide
  target_injective := by decide
def matching2 : Fin 2 ≃ Fin 2 := Equiv.refl (Fin 2)
def residualRank41 : Fin 4 → Fin 4 → DirectionKey :=
  ![![key41 5 1 (-1) (-1), key41 20 1 (-4) (-1),
      key41 5 1 1 (-1), key41 20 1 4 (-1)],
    ![key41 5 1 (-1) 1, key41 20 1 (-4) 1,
      key41 20 1 4 1, key41 5 1 1 1],
    ![key41 20 1 4 (-1), key41 5 1 1 (-1),
      key41 20 1 (-4) (-1), key41 5 1 (-1) (-1)],
    ![key41 20 1 4 1, key41 5 1 1 1,
      key41 5 1 (-1) 1, key41 20 1 (-4) 1]]
def residualRanking41 : GloballyRanked DirectionKey (Fin 4) (Fin 4) where
  rank := residualRank41
  source_injective := by decide
  target_injective := by decide
def residualMatching41 : Fin 4 ≃ Fin 4 := Equiv.swap (2 : Fin 4) (3 : Fin 4)
def residualProposalTrace41 : List (Fin 4 × Fin 4) :=
  [(0, 0), (1, 0), (2, 3), (3, 2), (1, 3), (1, 1)]
end Examples41
end TunnellMap


