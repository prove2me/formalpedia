-- Prove2me | Definitions.Def_RequestProject_TPSSefxCharge
-- name    : RequestProject_TPSSefxCharge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:15:15.195834+00:00
-- url     : https://prove2.me/theorems/9f50fc40-3e2c-4364-8e17-9323fb8f19ba
-- title:
--   TPSSefx Charge
-- statement:
--   Definitions and structural lemmas for TPSSefx Charge, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
def saleLoss (w p : G → ℝ) (t : ℝ) (g : G) : ℝ := trunc w p t g - p g
structure CStage (G : Type*) (n : ℕ) where
  /-- The agents that already hold a bundle. -/
  served : Finset (Fin n)
  /-- The goods each agent keeps. -/
  bundle : Fin n → Finset G
  /-- The sold goods charged to each agent. -/
  charge : Fin n → Finset G
  /-- The sale proceeds each agent holds. -/
  cash : Fin n → ℝ
  /-- The sale proceeds *put aside* for each agent: raised by selling goods charged to it, and
  not available to anybody else while the agent holds its bundle. -/
  resv : Fin n → ℝ
  /-- The free sale proceeds. -/
  bank : ℝ
namespace CStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
def soldSet (s : CStage G n) : Finset G := Finset.univ.biUnion s.charge
def pool (s : CStage G n) : Finset G :=
  Finset.univ \ (s.soldSet ∪ Finset.univ.biUnion s.bundle)
noncomputable def req (s : CStage G n) (j : Fin n) : ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j + eps
  else GeneralTPS.thr v p j
def CSafe (s : CStage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ s.req v p eps j) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ s.req v p eps j)
noncomputable def cost (s : CStage G n) (i j : Fin n) : ℝ :=
  truncBundle (v j) p (TPS n (v j) p) (s.bundle i) + s.cash i + s.resv i
    + ∑ g ∈ s.charge i, saleLoss (v j) p (TPS n (v j) p) g
noncomputable def total (s : CStage G n) : ℝ :=
  ∑ i, (vbarSum (v i) p (s.bundle i) + s.cash i)
def Good (s : CStage G n) : Prop :=
  (∀ i, i ∉ s.served → s.bundle i = ∅ ∧ s.charge i = ∅ ∧ s.cash i = 0 ∧ s.resv i = 0) ∧
  (∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)) ∧
  (∀ i j, i ≠ j → Disjoint (s.charge i) (s.charge j)) ∧
  (∀ i j, Disjoint (s.charge i) (s.bundle j)) ∧
  (∀ i, 0 ≤ s.cash i) ∧ (∀ i, 0 ≤ s.resv i) ∧ 0 ≤ s.bank ∧
  ((∑ i, s.cash i) + (∑ i, s.resv i) + s.bank = ∑ g ∈ s.soldSet, p g) ∧
  (∀ i ∈ s.served, GeneralTPS.thr v p i ≤ vbarSum (v i) p (s.bundle i) + s.cash i) ∧
  (∀ i ∈ s.served, ∀ j, s.CSafe v p eps i j) ∧
  (∀ i ∈ s.served, ∀ j, j ∉ s.served → s.cost v p i j ≤ 2 * GeneralTPS.thr v p j)
end CStage
namespace CStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
def toStage (s : CStage G n) : GeneralTPS.Stage G n :=
  ⟨s.served, s.bundle, s.soldSet, s.cash, s.bank + ∑ i, s.resv i⟩
end CStage
def emptyCStage (G : Type*) (n : ℕ) : CStage G n :=
  ⟨∅, fun _ => ∅, fun _ => ∅, fun _ => 0, fun _ => 0, 0⟩
def CImprovementStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ s : CStage G n, s.Good v p eps → s.served ≠ Finset.univ →
    ∃ s' : CStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))
section Descent
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end Descent
end ChargeTPS
end FairSelling


