-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
-- name    : LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:21:56.424706+00:00
-- url     : https://prove2.me/theorems/266ab9fc-cf30-4fae-8120-2b627e2005e9
-- title:
--   Pair
-- statement:
--   Definitions and structural lemmas for Pair, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Pair.lean

module
public import Mathlib.Util.Notation3
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)
@[inherit_doc prod] scoped[ZhangYeungPFR] notation3:100 "⟨" X ", " Y "⟩" => prod X Y
open scoped ZhangYeungPFR


