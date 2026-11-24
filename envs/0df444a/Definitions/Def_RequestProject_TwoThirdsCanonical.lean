-- Prove2me | Definitions.Def_RequestProject_TwoThirdsCanonical
-- name    : RequestProject_TwoThirdsCanonical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:11:32.461292+00:00
-- url     : https://prove2.me/theorems/1bbf3ef1-4aad-42b1-aaab-06990e9e9800
-- title:
--   Two Thirds Canonical
-- statement:
--   Definitions and structural lemmas for Two Thirds Canonical, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
structure Canonical (w p : G → ℝ) (μ t : ℝ) (k : ℕ) [NeZero k] (R : Finset G) (D : ℝ) where
  /-- The goods of each part. -/
  goods : Fin k → Finset G
  /-- The set `Sᵢ` of still-available goods the agent intends to sell. -/
  sell : Finset G
  /-- The good of `sell` whose sale funds the part, if any. -/
  src : Fin k → Option G
  /-- The money of the part that comes from the bank `D`. -/
  dcash : Fin k → ℝ
  /-- The money of the part that comes from the sale of `src`. -/
  scash : Fin k → ℝ
  goods_subset : ∀ j, goods j ⊆ R
  goods_disj : ∀ j j', j ≠ j' → Disjoint (goods j) (goods j')
  sell_subset : sell ⊆ R
  sell_disj : ∀ j, Disjoint sell (goods j)
  src_mem : ∀ j f, src j = some f → f ∈ sell
  dcash_nonneg : ∀ j, 0 ≤ dcash j
  scash_nonneg : ∀ j, 0 ≤ scash j
  dcash_sum : ∑ j, dcash j ≤ D
  /-- The parts funded by the sale of `f` share out at most the price of `f`. -/
  scash_sum : ∀ f ∈ sell, ∑ j ∈ Finset.univ.filter (fun j => src j = some f), scash j ≤ p f
  scash_zero : ∀ j, src j = none → scash j = 0
  /-- Condition 1: a good that is put up for sale has price at least `(1−ρ)·μ`. -/
  price_large : ∀ f ∈ sell, μ - t ≤ p f
  /-- Condition 2: every part is acceptable. -/
  acceptable : ∀ j, t ≤ vbarSum w p (goods j) + dcash j + scash j
  /-- Condition 2: apart from the special part, every part is pure or a singleton. -/
  pure_or_singleton : ∀ j, j ≠ 0 → (src j = none ∨ ∃ e, goods j = {e})
  /-- Condition 2: all the money of a singleton part comes from the sale of its associated
  good, so none of it comes from the bank. -/
  singleton_dcash : ∀ j, j ≠ 0 → src j ≠ none → dcash j = 0
  /-- Condition 3, in its non-strict form.

  The manuscript states this condition with a strict inequality, `t < v̄(e) + p(f)`.  The
  construction of Proposition 6 only ever produces the non-strict version: the good `e` of a
  singleton part is a *large* good, `v̄(e) ≥ (1−ρ)·μ`, and condition 1 gives `p(f) ≥ (1−ρ)·μ`,
  so that `v̄(e) + p(f) ≥ 2(1−ρ)·μ = ρ·μ = t` for `ρ = 2/3` — with equality in the borderline
  case.  Nothing in the development uses the strict form (the role condition 3 plays in the
  manuscript is played here by the hypothesis `hloss` of `losses_of_round`), so the condition is
  stated non-strictly. -/
  singleton_cond : ∀ j, j ≠ 0 → src j ≠ none → ∀ e ∈ goods j, ∀ f ∈ sell,
    t ≤ vbar w p e + p f
namespace Canonical
variable {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
def cash (C : Canonical w p μ t k R D) (j : Fin k) : ℝ := C.dcash j + C.scash j
def sold (C : Canonical w p μ t k R D) (J : Finset (Fin k)) : Finset G :=
  J.biUnion (fun j => (C.src j).toFinset)
end Canonical
end FairSelling


