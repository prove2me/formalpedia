-- Prove2me | Definitions.Def_RequestProject_TwoThirdsBudget
-- name    : RequestProject_TwoThirdsBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:16:08.66275+00:00
-- url     : https://prove2.me/theorems/19939c37-65fd-4d37-9d19-1525d12c662c
-- title:
--   Two Thirds Budget
-- statement:
--   Definitions and structural lemmas for Two Thirds Budget, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
noncomputable def eventCost {w p : G → ℝ} {μ : ℝ} {k : ℕ} (E : EquiMMS w p μ k)
    (Ea Fa : Finset G) (c : ℝ) : ℝ :=
  (∑ j, vbarSum w p (E.part j ∩ (Ea ∪ Fa))) + (∑ g ∈ E.sell ∩ (Ea ∪ Fa), p g)
    - (∑ g ∈ Fa, p g) + c
section Cost
variable {w p : G → ℝ} {μ : ℝ} {k : ℕ}
end Cost
end FairSelling


