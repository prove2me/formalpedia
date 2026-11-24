-- Prove2me | Definitions.Def_RequestProject_TPSSefxZero
-- name    : RequestProject_TPSSefxZero
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:11:37.368827+00:00
-- url     : https://prove2.me/theorems/fbd4b06b-6719-4ad5-8ea4-0d36ec6464b3
-- title:
--   TPSSefx Zero
-- statement:
--   Definitions and structural lemmas for TPSSefx Zero, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
def bval (w : G → ℝ) (S : Finset G) : ℝ := ∑ g ∈ S, w g
noncomputable def thr (v : Fin n → G → ℝ) (p : G → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p
abbrev St (G : Type*) (n : ℕ) := Finset (Fin n) × (Fin n → Finset G)
noncomputable def theta (v : Fin n → G → ℝ) (p : G → ℝ) (s : St G n) (j : Fin n) : ℝ :=
  if j ∈ s.1 then bval (v j) (s.2 j) else thr v p j
def GoodSt (v : Fin n → G → ℝ) (p : G → ℝ) (s : St G n) : Prop :=
  (∀ i, i ∉ s.1 → s.2 i = ∅) ∧
  (∀ i j, i ≠ j → Disjoint (s.2 i) (s.2 j)) ∧
  (∀ i ∈ s.1, thr v p i ≤ bval (v i) (s.2 i)) ∧
  (∀ i ∈ s.1, ∀ j : Fin n, ∀ g ∈ s.2 i, bval (v j) ((s.2 i).erase g) ≤ theta v p s j)
def pool (s : St G n) : Finset G := Finset.univ \ (Finset.univ.biUnion s.2)
def Claims (v : Fin n → G → ℝ) (p : G → ℝ) (s : St G n) (B : Finset G) (k : Fin n) : Prop :=
  if k ∈ s.1 then bval (v k) (s.2 k) < bval (v k) B else thr v p k ≤ bval (v k) B
def Claimed (v : Fin n → G → ℝ) (p : G → ℝ) (s : St G n) (B : Finset G) : Prop :=
  ∃ k, Claims v p s B k
end ZeroPrice
end FairSelling


