-- Prove2me | Definitions.Def_RequestProject_TPSApprox
-- name    : RequestProject_TPSApprox
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:40.923351+00:00
-- url     : https://prove2.me/theorems/65445b8c-4dca-47b3-a6cc-307c86c6ec41
-- title:
--   TPSApprox
-- statement:
--   Definitions and structural lemmas for TPSApprox, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
def trunc (w p : G → ℝ) (t : ℝ) (g : G) : ℝ := max (p g) (min (w g) t)
def truncBundle (w p : G → ℝ) (t : ℝ) (R : Finset G) : ℝ := ∑ g ∈ R, trunc w p t g
def Servable (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    (T : Finset (Fin n)) (R : Finset G) (D : ℝ) : Prop :=
  ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
    (∀ i, A i ⊆ R) ∧ F ⊆ R ∧
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
    (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ D + ∑ g ∈ F, p g) ∧
    (∀ i ∈ T, τ i ≤ vbarSum (v i) p (A i) + q i) ∧
    (∀ i, i ∉ T → A i = ∅ ∧ q i = 0)
end FairSelling


