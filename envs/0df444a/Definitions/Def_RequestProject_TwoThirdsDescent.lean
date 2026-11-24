-- Prove2me | Definitions.Def_RequestProject_TwoThirdsDescent
-- name    : RequestProject_TwoThirdsDescent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:14:04.305085+00:00
-- url     : https://prove2.me/theorems/1be0dedb-ddc3-475d-a0dd-0f522dfeaeef
-- title:
--   Two Thirds Descent
-- statement:
--   Definitions and structural lemmas for Two Thirds Descent, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsDescent.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
section Descent
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
end Descent
end FairSelling


