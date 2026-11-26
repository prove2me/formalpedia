-- Prove2me | Definitions.Def_TunnellMap_ShortInterval
-- name    : TunnellMap_ShortInterval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:47:48.747322+00:00
-- url     : https://prove2.me/theorems/a89bb713-9a6e-58dd-a5ff-f39db9398135
-- title:
--   Short Interval
-- statement:
--   Definitions and structural lemmas for Short Interval, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ShortInterval.lean

import Definitions.Def_TunnellMap_AffineLattice
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Rat.Floor
set_option autoImplicit true
namespace TunnellMap
namespace OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
def halfDiscriminant (A q b : ℤ) : ℤ :=
  let α := dot F.e₁ F.e₁
  let β := dot F.e₁ F.e₂
  let γ := dot F.e₂ F.e₂
  let δ := dot F.z F.e₁
  let ε := dot F.z F.e₂
  let ζ := dot F.z F.z
  let t := q * A
  (β * b + t * δ) ^ 2 -
    α * (γ * b ^ 2 + 2 * t * ε * b + t ^ 2 * ζ - A)
end OrthogonalFrame
end TunnellMap


