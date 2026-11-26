-- Prove2me | Definitions.Def_TunnellMap_ReducedBasisBound
-- name    : TunnellMap_ReducedBasisBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:52:08.072837+00:00
-- url     : https://prove2.me/theorems/813edfea-89d7-40f5-84d7-1c41687d5ddf
-- title:
--   Reduced Basis Bound
-- statement:
--   Definitions and structural lemmas for Reduced Basis Bound, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ReducedBasisBound.lean

import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
namespace TunnellMap
namespace OrderedGenerator
variable {p : Triple}
def gamma (F : OrthogonalFrame p) : ℤ := dot F.e₂ F.e₂
def IsLagrangeGaussReduced (F : OrthogonalFrame p) : Prop :=
  |2 * beta F| ≤ alpha F ∧ alpha F ≤ gamma F
end OrderedGenerator
end TunnellMap


