-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_Glue
-- name    : LeanPool_SteinerSpanners_Glue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:38.102173+00:00
-- url     : https://prove2.me/theorems/532f4aa2-6414-4e1e-81e3-25a3909a24f4
-- title:
--   Glue
-- statement:
--   Definitions and structural lemmas for Glue, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/Glue.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Glue
end HighDimSteinerSpanners.Proofs.Glue


