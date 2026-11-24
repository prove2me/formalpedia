-- Prove2me | Definitions.Def_RequestProject_TPSSefxGeneral
-- name    : RequestProject_TPSSefxGeneral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:14:22.821294+00:00
-- url     : https://prove2.me/theorems/f6f10101-6ea8-43e0-b726-aa770c1955a6
-- title:
--   TPSSefx General
-- statement:
--   Definitions and structural lemmas for TPSSefx General, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
def CSafeU (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (A : Fin n → Finset G) (q : Fin n → ℝ)
    (i j : Fin n) : Prop :=
  (vbarSum (v i) p (A i) + q i + eps ≥ vbarSum (v i) p (A j) + q j) ∨
  (q j = 0 ∧ (∀ g ∈ A j, p g ≤ v j g) ∧
    ∀ g ∈ A j, vbarSum (v i) p (A i) + q i + eps ≥ vbarSum (v i) p (A j \ {g}) + p g)
noncomputable def thr (v : Fin n → G → ℝ) (p : G → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p
structure Stage (G : Type*) (n : ℕ) where
  /-- The agents that already hold a bundle. -/
  served : Finset (Fin n)
  /-- The bundle of goods held by each agent. -/
  bundle : Fin n → Finset G
  /-- The goods that have been sold. -/
  soldSet : Finset G
  /-- The sale proceeds held by each agent. -/
  cash : Fin n → ℝ
  /-- The sale proceeds that are not yet allocated. -/
  bank : ℝ
namespace Stage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
def pool (s : Stage G n) : Finset G :=
  Finset.univ \ (s.soldSet ∪ Finset.univ.biUnion s.bundle)
noncomputable def guar (s : Stage G n) (j : Fin n) : ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j else thr v p j
def Safe (s : Stage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ s.guar v p j + eps) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ s.guar v p j + eps)
noncomputable def total (s : Stage G n) : ℝ :=
  ∑ i, (vbarSum (v i) p (s.bundle i) + s.cash i)
def Good (s : Stage G n) : Prop :=
  (∀ i, i ∉ s.served → s.bundle i = ∅ ∧ s.cash i = 0) ∧
  (∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)) ∧
  (∀ i, Disjoint s.soldSet (s.bundle i)) ∧
  (∀ i, 0 ≤ s.cash i) ∧ 0 ≤ s.bank ∧
  ((∑ i, s.cash i) + s.bank = ∑ g ∈ s.soldSet, p g) ∧
  (∀ i ∈ s.served, thr v p i ≤ vbarSum (v i) p (s.bundle i) + s.cash i) ∧
  (∀ i ∈ s.served, ∀ j, s.Safe v p eps i j) ∧
  (∀ j, j ∉ s.served → (2 * ((n : ℝ) - s.served.card) - 1) * thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + s.bank)
end Stage
def emptyStage (G : Type*) (n : ℕ) : Stage G n :=
  ⟨∅, fun _ => ∅, ∅, fun _ => 0, 0⟩
noncomputable def totalBound (v : Fin n → G → ℝ) (p : G → ℝ) : ℝ :=
  (∑ i, vbarSum (v i) p Finset.univ) + ∑ g, p g
def ImprovementStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ s : Stage G n, s.Good v p eps → s.served ≠ Finset.univ →
    ∃ s' : Stage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))
section Descent
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end Descent
end GeneralTPS
end FairSelling


