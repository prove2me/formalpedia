-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
-- name    : LeanPool_SteinerSpanners_CSP_Expurgation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:49:07.369439+00:00
-- url     : https://prove2.me/theorems/93b54af7-f164-48ac-a10d-70b24809fb4c
-- title:
--   Expurgation
-- statement:
--   Definitions and structural lemmas for Expurgation, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Expurgation.lean

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Bernoulli
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.CSP
noncomputable section Helpers
end Helpers
end HighDimSteinerSpanners.Proofs.CSP


