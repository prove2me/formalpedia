-- Prove2me | Definitions.Def_RequestProject_TPSSefxPhase
-- name    : RequestProject_TPSSefxPhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:19:33.455768+00:00
-- url     : https://prove2.me/theorems/3545522a-08e3-45ec-857b-66c1129ca1e7
-- title:
--   TPSSefx Phase
-- statement:
--   Definitions and structural lemmas for TPSSefx Phase, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
def PureGood (v : Fin n → G → ℝ) (p : G → ℝ) (served : Finset (Fin n)) (g : G) : Prop :=
  ∀ j, j ∉ served → saleLoss (v j) p (TPS n (v j) p) g = 0
structure PStage (G : Type*) (n : ℕ) where
  /-- The agents that already hold a bundle. -/
  served : Finset (Fin n)
  /-- The goods each agent keeps. -/
  bundle : Fin n → Finset G
  /-- The goods sold *inside* an agent's own package: the agent holds their whole price, as cash
  or put aside, and can undo the sale at any moment. -/
  own : Fin n → Finset G
  /-- The pure goods an agent has sold in a large-good step: only part of the proceeds was
  handed out, the rest is free, and the agent keeps the charge for ever. -/
  ext : Fin n → Finset G
  /-- The sale proceeds each agent holds. -/
  cash : Fin n → ℝ
  /-- The sale proceeds put aside for each agent. -/
  resv : Fin n → ℝ
  /-- The free sale proceeds. -/
  bank : ℝ
namespace PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
def charge (s : PStage G n) (i : Fin n) : Finset G := s.own i ∪ s.ext i
def sold (s : PStage G n) : Finset G := Finset.univ.biUnion s.charge
def pool (s : PStage G n) : Finset G :=
  Finset.univ \ (s.sold ∪ Finset.univ.biUnion s.bundle)
noncomputable def req (s : PStage G n) (j : Fin n) : ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j + eps
  else GeneralTPS.thr v p j
def PSafe (s : PStage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ s.req v p eps j) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ s.req v p eps j)
def ShareOK (s : PStage G n) (i : Fin n) (g : G) : Prop :=
  s.bundle i = ∅ ∧ s.own i = ∅ ∧ s.resv i = 0 ∧ s.cash i ≤ p g ∧
    ∀ g' ∈ s.ext i, g' ≠ g → PureGood v p s.served g'
noncomputable def cost (s : PStage G n) (i j : Fin n) : ℝ :=
  truncBundle (v j) p (TPS n (v j) p) (s.bundle i) + s.cash i + s.resv i
    + ∑ g ∈ s.own i, saleLoss (v j) p (TPS n (v j) p) g
    + ∑ g ∈ s.ext i, saleLoss (v j) p (TPS n (v j) p) g
noncomputable def total (s : PStage G n) : ℝ :=
  ∑ i, (vbarSum (v i) p (s.bundle i) + s.cash i)
structure Good (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : PStage G n) : Prop where
  /-- An unserved agent holds nothing. -/
  unserved : ∀ i, i ∉ s.served →
    s.bundle i = ∅ ∧ s.own i = ∅ ∧ s.ext i = ∅ ∧ s.cash i = 0 ∧ s.resv i = 0
  /-- Bundles are pairwise disjoint. -/
  bundle_disj : ∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)
  /-- Sold goods are in nobody's bundle. -/
  charge_bundle : ∀ i j, Disjoint (s.charge i) (s.bundle j)
  /-- Self-financed sales belong to one agent only. -/
  own_disj : ∀ i j, i ≠ j → Disjoint (s.own i) (s.own j)
  /-- A self-financed sale is never also a large-good sale. -/
  own_ext : ∀ i j, Disjoint (s.own i) (s.ext j)
  /-- A large-good sale is either *pure* — its price already dominates its truncated
  contribution for every unserved agent, so carrying it costs nobody anything — or *shared*:
  the agent charged with it holds nothing but a slice of its proceeds. -/
  ext_ok : ∀ i, ∀ g ∈ s.ext i, PureGood v p s.served g ∨ s.ShareOK v p i g
  /-- Only a pure large-good sale may be charged to more than one agent. -/
  ext_uniq : ∀ i i', i ≠ i' → ∀ g ∈ s.ext i, g ∈ s.ext i' → PureGood v p s.served g
  cash_nonneg : ∀ i, 0 ≤ s.cash i
  resv_nonneg : ∀ i, 0 ≤ s.resv i
  bank_nonneg : 0 ≤ s.bank
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
end PStage
namespace PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
open Classical in
/-- The charged stage underlying a phase-structured stage: the pure goods of `ext` are attributed
to the *first* agent charged with them, which turns the cover of the sold goods into a
partition.  This changes no cost, because pure goods cost nothing. -/
noncomputable def toCStage (s : PStage G n) : ChargeTPS.CStage G n :=
  ⟨s.served, s.bundle,
    fun i => s.own i ∪ (s.ext i).filter (fun g => ∀ k, g ∈ s.charge k → i ≤ k),
    s.cash, s.resv, s.bank⟩
end PStage
def emptyPStage (G : Type*) (n : ℕ) : PStage G n :=
  ⟨∅, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => 0, fun _ => 0, 0⟩
def PImprovementStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ s : PStage G n, s.Good v p eps → s.served ≠ Finset.univ →
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))
section Descent
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end Descent
end PhaseTPS
end FairSelling


