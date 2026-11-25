-- Prove2me | Definitions.Def_Fekete
-- name    : Fekete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:33:38.673878+00:00
-- url     : https://prove2.me/theorems/fef49aec-24db-4293-97aa-43bb41c7bd46
-- title:
--   Fekete
-- statement:
--   Definitions and structural lemmas for Fekete, from Brian Sanders (Egly443/lean-fekete; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nearly subadditive sequences and Fekete's lemma beyond Mathlib development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete.lean

module
public import Definitions.Def_Fekete_BoundedDefect
public import Definitions.Def_Fekete_DeBruijnErdos
public import Definitions.Def_Fekete_Sharpness
public import Definitions.Def_Fekete_Superadditive
public import Definitions.Def_Fekete_SupermultiplicativeCounterexample
public import Definitions.Def_Fekete_Window
set_option autoImplicit true
@[expose] public section


