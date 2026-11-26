-- Prove2me | Definitions.Def_TunnellMap_QuadraticRoots
-- name    : TunnellMap_QuadraticRoots
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:51:53.583897+00:00
-- url     : https://prove2.me/theorems/9d5709d4-4c1c-4711-a072-dfd07353cbde
-- title:
--   Quadratic Roots
-- statement:
--   Definitions and structural lemmas for Quadratic Roots, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean

import Definitions.Def_TunnellMap_ShortInterval
set_option autoImplicit true
namespace TunnellMap
def quadraticEquation (α c d a : ℤ) : Prop :=
  α * a ^ 2 + 2 * c * a + d = 0
def quadraticHalfDiscriminant (α c d : ℤ) : ℤ := c ^ 2 - α * d
namespace OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
def affineQuadratic (A q a b : ℤ) : ℤ :=
  let α := dot F.e₁ F.e₁
  let β := dot F.e₁ F.e₂
  let γ := dot F.e₂ F.e₂
  let δ := dot F.z F.e₁
  let ε := dot F.z F.e₂
  let ζ := dot F.z F.z
  let t := q * A
  α * a ^ 2 + 2 * (β * b + t * δ) * a +
    γ * b ^ 2 + 2 * t * ε * b + t ^ 2 * ζ - A
end OrthogonalFrame
end TunnellMap


