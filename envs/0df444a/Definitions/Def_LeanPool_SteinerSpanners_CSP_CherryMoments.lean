-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments
-- name    : LeanPool_SteinerSpanners_CSP_CherryMoments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:50:17.797807+00:00
-- url     : https://prove2.me/theorems/294bc923-c4ca-463b-9df4-3bf0841f4bbe
-- title:
--   Cherry Moments
-- statement:
--   Definitions and structural lemmas for Cherry Moments, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/CherryMoments.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.CSP
noncomputable section Helpers
end Helpers
end HighDimSteinerSpanners.Proofs.CSP


