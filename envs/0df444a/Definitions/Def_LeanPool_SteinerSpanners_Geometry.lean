-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_Geometry
-- name    : LeanPool_SteinerSpanners_Geometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:14.187587+00:00
-- url     : https://prove2.me/theorems/608329cd-f90b-412e-a529-3f46dbf03e4c
-- title:
--   Geometry
-- statement:
--   Definitions and structural lemmas for Geometry, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Geometry.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Geometry
noncomputable section
end
end HighDimSteinerSpanners.Proofs.Geometry


