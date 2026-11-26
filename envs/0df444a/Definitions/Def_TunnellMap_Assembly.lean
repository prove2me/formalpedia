-- Prove2me | Definitions.Def_TunnellMap_Assembly
-- name    : TunnellMap_Assembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:40:03.031603+00:00
-- url     : https://prove2.me/theorems/09ca1a79-9353-54c0-bde3-aac76e803389
-- title:
--   Assembly
-- statement:
--   Definitions and structural lemmas for Assembly, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean

import Definitions.Def_TunnellMap_Basic
set_option autoImplicit true
namespace TunnellMap
section AbstractAssembly
variable {E O A : Type*}
def assemble (even : E ≃ A) (odd : O ≃ A) : E ⊕ O → A
  | Sum.inl e => even e
  | Sum.inr o => odd o
end AbstractAssembly
def conditionalTunnellMap {n : ℤ} (odd : BOddRep n ≃ ARep n) :
    BEvenParam n ⊕ BOddRep n → ARep n :=
  assemble (evenEquiv n) odd
end TunnellMap


