-- Prove2me | Definitions.Def_RequestProject_EquiMMS
-- name    : RequestProject_EquiMMS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:13:21.921627+00:00
-- url     : https://prove2.me/theorems/276fff84-30ed-4c76-8faa-12e5d0e93fa7
-- title:
--   Equi MMS
-- statement:
--   Definitions and structural lemmas for Equi MMS, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
structure EquiMMS (w p : G → ℝ) (μ : ℝ) (k : ℕ) where
  /-- The goods of each part. -/
  part : Fin k → Finset G
  /-- The set `Sᵢ` of goods the agent intends to sell. -/
  sell : Finset G
  /-- The share of the proceeds that goes to each part. -/
  cash : Fin k → ℝ
  part_disj : ∀ j j', j ≠ j' → Disjoint (part j) (part j')
  sell_disj : ∀ j, Disjoint sell (part j)
  cash_nonneg : ∀ j, 0 ≤ cash j
  cash_sum : ∑ j, cash j = ∑ g ∈ sell, p g
  value : ∀ j, vbarSum w p (part j) + cash j = μ
  /-- A good the agent intends to sell is not worth more to it than its price: the readjustment
  of Lemma 6 lowers the value of such a good to its price, since the partition only uses the
  price. -/
  sell_price : ∀ e ∈ sell, w e ≤ p e
noncomputable def EquiMMS.budget {w p : G → ℝ} {μ : ℝ} {k : ℕ} (E : EquiMMS w p μ k)
    (R : Finset G) (D : ℝ) : ℝ :=
  (∑ j, vbarSum w p (E.part j ∩ R)) + (∑ g ∈ E.sell ∩ R, p g) + D
end FairSelling


