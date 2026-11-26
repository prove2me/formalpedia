-- Prove2me | Definitions.Def_TunnellMap_ComputableDirection
-- name    : TunnellMap_ComputableDirection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:21:08.339903+00:00
-- url     : https://prove2.me/theorems/1c5883fd-5f52-5350-8574-5f7a3f20e2a3
-- title:
--   Computable Direction
-- statement:
--   Definitions and structural lemmas for Computable Direction, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean

import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
namespace TunnellMap
open Polynomial
def tripleGcd (v : Triple) : ℤ := gcd (gcd v.x v.y) v.z
def primitivePartExec (v : Triple) : Triple :=
  ⟨v.x / tripleGcd v, v.y / tripleGcd v, v.z / tripleGcd v⟩
def primitiveDirectionExec (v : Triple) : Triple :=
  orientDirection (primitivePartExec v)
def primitiveKey (v : Triple) : DirectionKey :=
  ⟨qForm v, v.x, v.y, v.z⟩
def keyLtExec (k₁ k₂ : DirectionKey) : Bool := DirectionKey.blt k₁ k₂
def keyLeExec (k₁ k₂ : DirectionKey) : Bool := !keyLtExec k₂ k₁
def directionKeyExec (v : Triple) : DirectionKey :=
  primitiveKey (primitiveDirectionExec v)
end TunnellMap


