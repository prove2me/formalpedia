-- Prove2me | Definitions.Def_Tablet_smallPieceCount
-- name    : Tablet_smallPieceCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:58:47.556125+00:00
-- url     : https://prove2.me/theorems/eaf511ea-1202-5c44-a748-8111e4b1ed96
-- title:
--   small Piece Count
-- statement:
--   Definitions and structural lemmas for small Piece Count, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/smallPieceCount.lean

import Definitions.Def_Tablet_IsGeodesicResolution
set_option autoImplicit false
open Set
noncomputable def smallPieceCount {E : Type*} [MetricSpace E] (γ : Curve E) (δ : ℝ) : ℕ :=
-- BODY
  sInf { c : ℕ | ∃ k : ℕ, ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧
    c = ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card }


