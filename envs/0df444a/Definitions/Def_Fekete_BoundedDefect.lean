-- Prove2me | Definitions.Def_Fekete_BoundedDefect
-- name    : Fekete_BoundedDefect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:25:04.375957+00:00
-- url     : https://prove2.me/theorems/32e156e0-6c7a-5e8c-9018-393ea91b61e0
-- title:
--   Bounded Defect
-- statement:
--   Definitions and structural lemmas for Bounded Defect, from Brian Sanders (Egly443/lean-fekete; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nearly subadditive sequences and Fekete's lemma beyond Mathlib development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/BoundedDefect.lean

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Filter
open scoped Topology


