-- Prove2me | Definitions.Def_NagataFactoriality_Basic_Divisibility
-- name    : NagataFactoriality_Basic_Divisibility
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:46:54.213374+00:00
-- url     : https://prove2.me/theorems/56a4673f-1f25-442f-b52e-8f6688d606f9
-- title:
--   Divisibility
-- statement:
--   Definitions and structural lemmas for Divisibility, from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz (Arthur742Ramos/NagataFactoriality; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Prime-generated Nagata factoriality theorem for Noetherian integral domains development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
set_option autoImplicit false
namespace NagataFactoriality
open scoped BigOperators
def listProd {α : Type*} [CommMonoid α] : List α → α
  | [] => 1
  | a :: as => a * listProd as
end NagataFactoriality


