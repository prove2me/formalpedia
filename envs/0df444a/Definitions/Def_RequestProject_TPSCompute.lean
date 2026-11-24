-- Prove2me | Definitions.Def_RequestProject_TPSCompute
-- name    : RequestProject_TPSCompute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:51.302814+00:00
-- url     : https://prove2.me/theorems/b48e5ed8-5cf3-4cbf-9202-2be508016526
-- title:
--   TPSCompute
-- statement:
--   Definitions and structural lemmas for TPSCompute, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
def NoBreak (v p : G → ℝ) (a c : ℝ) : Prop :=
  ∀ g, (v g ≤ a ∨ c ≤ v g) ∧ (p g ≤ a ∨ c ≤ p g)
open Classical in
/-- The goods whose contribution to `f` equals `t` throughout the interval `[a, c]`. -/
noncomputable def slopeGoods (v p : G → ℝ) (a c : ℝ) : Finset G :=
  Finset.univ.filter (fun g => c ≤ v g ∧ p g ≤ a)
noncomputable def flatConst (v p : G → ℝ) (a c : ℝ) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g => ¬ (c ≤ v g ∧ p g ≤ a)), max (p g) (min (v g) a)
open Classical in
/-- The breakpoints of the truncated-proportional map: `{0} ∪ {v(g) : g} ∪ {p(g) : g}`. -/
noncomputable def breakpoints (v p : G → ℝ) : Finset ℝ :=
  insert 0 ((Finset.univ.image v) ∪ (Finset.univ.image p))
end FairSelling


