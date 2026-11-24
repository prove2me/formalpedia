-- Prove2me | Definitions.Def_RequestProject_TwoThirdsGlue
-- name    : RequestProject_TwoThirdsGlue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:13:17.366279+00:00
-- url     : https://prove2.me/theorems/362347a3-637b-4530-a49e-9506ae1d2e06
-- title:
--   Two Thirds Glue
-- statement:
--   Definitions and structural lemmas for Two Thirds Glue, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsGlue.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
def CanonExists (w p : G → ℝ) (μ t : ℝ) (k : ℕ) (R : Finset G) (D : ℝ) : Prop :=
  ∀ h : 0 < k, Nonempty (@Canonical G _ w p μ t k ⟨Nat.pos_iff_ne_zero.mp h⟩ R D)
end FairSelling


