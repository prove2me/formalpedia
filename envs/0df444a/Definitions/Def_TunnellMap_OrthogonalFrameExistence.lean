-- Prove2me | Definitions.Def_TunnellMap_OrthogonalFrameExistence
-- name    : TunnellMap_OrthogonalFrameExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:47:37.773722+00:00
-- url     : https://prove2.me/theorems/338fae6c-2541-49cd-be0f-7c5742718b03
-- title:
--   Orthogonal Frame Existence
-- statement:
--   Definitions and structural lemmas for Orthogonal Frame Existence, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrthogonalFrameExistence.lean

import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
namespace TunnellMap
def tripleGCD (p : Triple) : ℕ := Int.gcd (Int.gcd p.x p.y : ℤ) p.z
def tripleBezout (p : Triple) : Triple :=
  let g : ℤ := Int.gcd p.x p.y
  let c := g.gcdA p.z
  ⟨p.x.gcdA p.y * c, p.x.gcdB p.y * c, g.gcdB p.z⟩
end TunnellMap


