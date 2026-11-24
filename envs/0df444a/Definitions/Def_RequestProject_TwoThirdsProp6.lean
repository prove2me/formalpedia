-- Prove2me | Definitions.Def_RequestProject_TwoThirdsProp6
-- name    : RequestProject_TwoThirdsProp6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:12:18.763719+00:00
-- url     : https://prove2.me/theorems/0dd15beb-b35e-485d-a37f-771a96b7441d
-- title:
--   Two Thirds Prop6
-- statement:
--   Definitions and structural lemmas for Two Thirds Prop6, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
structure FillOut (w p : G → ℝ) (ε : ℝ) (m : ℕ) (Res : Finset G) (d r : ℝ) (f₀ : Option G) where
  /-- The goods of each part. -/
  goods : ℕ → Finset G
  /-- The goods that are sold. -/
  sell : Finset G
  /-- The good whose sale funds each part, if any. -/
  src : ℕ → Option G
  /-- The banked money of each part. -/
  dcash : ℕ → ℝ
  /-- The sale proceeds of each part. -/
  scash : ℕ → ℝ
  goods_subset : ∀ j, goods j ⊆ Res
  goods_disj : ∀ j j', j ≠ j' → Disjoint (goods j) (goods j')
  goods_zero : ∀ j, m ≤ j → goods j = ∅
  sell_subset : sell ⊆ Res ∪ f₀.toFinset
  sell_disj : ∀ j, Disjoint sell (goods j)
  src_mem : ∀ j f, src j = some f → f ∈ sell
  src_zero : ∀ j, m ≤ j → src j = none
  dcash_nonneg : ∀ j, 0 ≤ dcash j
  scash_nonneg : ∀ j, 0 ≤ scash j
  dcash_zero : ∀ j, m ≤ j → dcash j = 0
  dcash_sum : ∑ j ∈ Finset.range m, dcash j ≤ d
  scash_sum : ∀ f, ∑ j ∈ (Finset.range m).filter (fun j => src j = some f), scash j
    ≤ (if f₀ = some f then r else p f)
  scash_zero : ∀ j, src j = none → scash j = 0
  price_large : ∀ f ∈ sell, ε ≤ p f
  acceptable : ∀ j < m, 2 * ε ≤ vbarSum w p (goods j) + dcash j + scash j
  pure_or_singleton : ∀ j, j ≠ 0 → j < m → (src j = none ∨ ∃ e, goods j = {e})
  singleton_dcash : ∀ j, j ≠ 0 → src j ≠ none → dcash j = 0
  singleton_large : ∀ j, j ≠ 0 → src j ≠ none → ∀ e ∈ goods j, ε ≤ vbar w p e
end FairSelling


