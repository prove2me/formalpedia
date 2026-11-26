-- Prove2me | Definitions.Def_Tablet_GeodesicPairing
-- name    : Tablet_GeodesicPairing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:48:18.300038+00:00
-- url     : https://prove2.me/theorems/a5eb10d4-f551-5605-ad9a-688f5db0ee11
-- title:
--   Geodesic Pairing
-- statement:
--   Definitions and structural lemmas for Geodesic Pairing, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/GeodesicPairing.lean

import Definitions.Def_Tablet_IsGeodesicOn
set_option autoImplicit false
open Set
structure GeodesicPairing (E : Type*) [MetricSpace E] where
-- BODY
  G : E → E → Curve E
  len_eq : ∀ x y : E, (G x y).len = dist x y
  start_eq : ∀ x y : E, (G x y).toFun 0 = x
  end_eq : ∀ x y : E, (G x y).toFun (G x y).len = y
  isGeodesic : ∀ x y : E, IsGeodesicOn (G x y) 0 (G x y).len
  reversal : ∀ x y : E, ∀ t ∈ Set.Icc (0:ℝ) (dist x y), (G y x).toFun t = (G x y).toFun (dist x y - t)


