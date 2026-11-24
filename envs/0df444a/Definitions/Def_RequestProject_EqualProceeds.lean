-- Prove2me | Definitions.Def_RequestProject_EqualProceeds
-- name    : RequestProject_EqualProceeds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:02.827821+00:00
-- url     : https://prove2.me/theorems/c1850ba7-3f2d-445f-bcbd-7814b1f04019
-- title:
--   Equal Proceeds
-- statement:
--   Definitions and structural lemmas for Equal Proceeds, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
def Outcome.EqualProceeds (p : G → ℝ) (o : Outcome G n) : Prop :=
  ∀ i, o.money i = (∑ g ∈ o.sold, p g) / n
def MMSEPset (n : ℕ) (v p : G → ℝ) : Set ℝ :=
  {r | ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧ ∀ j, r ≤ util v o j}
noncomputable def MMSEP (n : ℕ) (v p : G → ℝ) : ℝ := sSup (MMSEPset n v p)
end FairSelling


