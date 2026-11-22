-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_CSP_EdgeMoments
-- name    : LeanPool_SteinerSpanners_CSP_EdgeMoments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:50:44.917925+00:00
-- url     : https://prove2.me/theorems/12cbfee5-8ff3-4654-8b5e-bf99423c79d6
-- title:
--   Edge Moments
-- statement:
--   Definitions and structural lemmas for Edge Moments, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/EdgeMoments.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.CSP
noncomputable section Helpers
end Helpers
end HighDimSteinerSpanners.Proofs.CSP


