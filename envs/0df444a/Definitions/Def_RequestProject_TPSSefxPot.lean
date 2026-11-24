-- Prove2me | Definitions.Def_RequestProject_TPSSefxPot
-- name    : RequestProject_TPSSefxPot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:19:52.34703+00:00
-- url     : https://prove2.me/theorems/740589f7-4bcf-4b82-909d-ff5e038d850a
-- title:
--   TPSSefx Pot
-- statement:
--   Definitions and structural lemmas for TPSSefx Pot, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
structure QStage (G : Type*) (n : ℕ) where
  /-- The agents that already hold a bundle. -/
  served : Finset (Fin n)
  /-- The goods each agent keeps. -/
  bundle : Fin n → Finset G
  /-- The goods sold *inside* an agent's own package: the agent holds their whole price, as cash
  or put aside, and can undo the sale at any moment. -/
  own : Fin n → Finset G
  /-- The good — there is at most one — a *cut* of whose proceeds the agent holds.  The agent is
  then charged with that good. -/
  src : Fin n → Finset G
  /-- The sale proceeds each agent holds. -/
  cash : Fin n → ℝ
  /-- The sale proceeds put aside for each agent. -/
  resv : Fin n → ℝ
  /-- The sale proceeds nobody holds. -/
  bank : ℝ
namespace QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
def cutSet (s : QStage G n) : Finset G := Finset.univ.biUnion s.src
def sold (s : QStage G n) : Finset G := (Finset.univ.biUnion s.own) ∪ s.cutSet
def pool (s : QStage G n) : Finset G :=
  Finset.univ \ (s.sold ∪ Finset.univ.biUnion s.bundle)
def holders (s : QStage G n) (g : G) : Finset (Fin n) :=
  Finset.univ.filter (fun i => g ∈ s.src i)
noncomputable def pot (s : QStage G n) (p : G → ℝ) (g : G) : ℝ :=
  p g - ∑ i ∈ s.holders g, s.cash i
noncomputable def freeBank (s : QStage G n) (p : G → ℝ) : ℝ :=
  s.bank - ∑ g ∈ s.cutSet, s.pot p g
noncomputable def req (s : QStage G n) (j : Fin n) : ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j + eps
  else GeneralTPS.thr v p j
def PSafe (s : QStage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ s.req v p eps j) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ s.req v p eps j)
noncomputable def cost (s : QStage G n) (i j : Fin n) : ℝ :=
  truncBundle (v j) p (TPS n (v j) p) (s.bundle i) + s.cash i + s.resv i
    + ∑ g ∈ s.own i, saleLoss (v j) p (TPS n (v j) p) g
    + ∑ g ∈ s.src i,
        (saleLoss (v j) p (TPS n (v j) p) g + min (s.pot p g) (GeneralTPS.thr v p j))
noncomputable def total (s : QStage G n) : ℝ :=
  ∑ i, (vbarSum (v i) p (s.bundle i) + s.cash i)
structure Good (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : QStage G n) : Prop where
  /-- An unserved agent holds nothing. -/
  unserved : ∀ i, i ∉ s.served →
    s.bundle i = ∅ ∧ s.own i = ∅ ∧ s.src i = ∅ ∧ s.cash i = 0 ∧ s.resv i = 0
  /-- Bundles are pairwise disjoint. -/
  bundle_disj : ∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)
  /-- Sold goods are in nobody's bundle. -/
  sold_bundle : ∀ i, Disjoint s.sold (s.bundle i)
  /-- Self-financed sales belong to one agent only. -/
  own_disj : ∀ i j, i ≠ j → Disjoint (s.own i) (s.own j)
  /-- A self-financed sale is never a cut. -/
  own_cut : ∀ i j, Disjoint (s.own i) (s.src j)
  /-- An agent holds a slice of at most one cut good. -/
  src_card : ∀ i, (s.src i).card ≤ 1
  /-- An agent holding a slice holds nothing else. -/
  cutter : ∀ i, s.src i ≠ ∅ → s.bundle i = ∅ ∧ s.own i = ∅ ∧ s.resv i = 0
  cash_nonneg : ∀ i, 0 ≤ s.cash i
  resv_nonneg : ∀ i, 0 ≤ s.resv i
  /-- The slices of a cut good never exceed its price. -/
  pot_nonneg : ∀ g ∈ s.cutSet, 0 ≤ s.pot p g
  /-- The pots are part of the bank. -/
  bank_pot : ∑ g ∈ s.cutSet, s.pot p g ≤ s.bank
  /-- Self-financing: an agent holds the whole price of the goods it sold on its own. -/
  self_fin : ∀ i, ∑ g ∈ s.own i, p g ≤ s.cash i + s.resv i
  /-- The money equation. -/
  money : (∑ i, s.cash i) + (∑ i, s.resv i) + s.bank = ∑ g ∈ s.sold, p g
  /-- Every served agent is above its threshold. -/
  share : ∀ i ∈ s.served, GeneralTPS.thr v p i ≤ vbarSum (v i) p (s.bundle i) + s.cash i
  /-- Every package is safe for everybody. -/
  safe : ∀ i ∈ s.served, ∀ j, s.PSafe v p eps i j
  /-- Every package costs every unserved agent at most `2τ`. -/
  cost_le : ∀ i ∈ s.served, ∀ j, j ∉ s.served → s.cost v p i j ≤ 2 * GeneralTPS.thr v p j
  /-- A slice is never bigger than the threshold of an agent that is still unserved. -/
  slice_le : ∀ i, s.src i ≠ ∅ → ∀ j, j ∉ s.served → s.cash i ≤ GeneralTPS.thr v p j
end QStage
namespace QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
noncomputable def toStage (s : QStage G n) : GeneralTPS.Stage G n :=
  ⟨s.served, s.bundle, s.sold, s.cash, s.bank + ∑ i, s.resv i⟩
end QStage
def emptyQStage (G : Type*) (n : ℕ) : QStage G n :=
  ⟨∅, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => 0, fun _ => 0, 0⟩
def QImprovementStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ s : QStage G n, s.Good v p eps → s.served ≠ Finset.univ →
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))
section Descent
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end Descent
end PotTPS
end FairSelling


