-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_CSP_Existence
-- name    : LeanPool_SteinerSpanners_CSP_Existence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:51:32.912797+00:00
-- url     : https://prove2.me/theorems/98fdef37-74ab-4970-8e26-c5c7dca5394c
-- title:
--   Existence
-- statement:
--   Definitions and structural lemmas for Existence, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Existence.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Convert
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_ClosePairs
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.CSP
noncomputable section Helpers
abbrev Assignment (C₁ r : ℕ) := Fin (2 ^ cspL C₁ * r) → Fin (cspQ C₁)
abbrev Outcome (C₁ r : ℕ) := cspIota (2 ^ cspL C₁ * r) (cspQ C₁) → Bool
end Helpers
end HighDimSteinerSpanners.Proofs.CSP


