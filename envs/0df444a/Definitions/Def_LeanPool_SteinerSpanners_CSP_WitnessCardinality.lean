-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
-- name    : LeanPool_SteinerSpanners_CSP_WitnessCardinality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:56.86054+00:00
-- url     : https://prove2.me/theorems/99e820b0-cc03-45b1-be5b-9b76925ddc3c
-- title:
--   Witness Cardinality
-- statement:
--   Definitions and structural lemmas for Witness Cardinality, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessCardinality.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.CSP
noncomputable section Helpers
end Helpers
end HighDimSteinerSpanners.Proofs.CSP


