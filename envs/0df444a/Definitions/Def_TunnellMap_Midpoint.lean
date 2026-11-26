-- Prove2me | Definitions.Def_TunnellMap_Midpoint
-- name    : TunnellMap_Midpoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:39:20.404807+00:00
-- url     : https://prove2.me/theorems/bc1e4d2f-ec3f-50b8-8d5e-6ef7193e929f
-- title:
--   Midpoint
-- statement:
--   Definitions and structural lemmas for Midpoint, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean

import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
namespace TunnellMap
def qForm (p : Triple) : ℤ :=
  2 * p.x ^ 2 + p.y ^ 2 + 2 * p.z ^ 2
def bLift {n : ℤ} (p : BOddRep n) : Triple :=
  ⟨p.1.x, p.1.y, 2 * p.1.z⟩
def aLift {n : ℤ} (p : ARep n) : Triple :=
  ⟨p.1.x, p.1.y, 4 * p.1.z⟩
def IsHalfSum (h E F : Triple) : Prop :=
  2 * h.x = E.x + F.x ∧
    2 * h.y = E.y + F.y ∧
    2 * h.z = E.z + F.z
def IsHalfDiff (h E F : Triple) : Prop :=
  2 * h.x = E.x - F.x ∧
    2 * h.y = E.y - F.y ∧
    2 * h.z = E.z - F.z
end TunnellMap


