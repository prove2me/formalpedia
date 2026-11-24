-- Prove2me | Definitions.Def_RequestProject_TPSSefxPhaseStep
-- name    : RequestProject_TPSSefxPhaseStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:20:48.094414+00:00
-- url     : https://prove2.me/theorems/6a91cedc-eff7-4a73-addc-a2b44e3e3204
-- title:
--   TPSSefx Phase Step
-- statement:
--   Definitions and structural lemmas for TPSSefx Phase Step, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseStep.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhase
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
def PCarrierReassign : Prop :=
  ∀ (_hn : 0 < n) (_hp : ∀ g, 0 ≤ p g) (_heps : 0 ≤ eps)
    {s : PStage G n} (_hs : s.Good v p eps) {k : Fin n}
    {S S₀own S₀ext : Finset G}
    (_hSpool : S ⊆ s.pool) (_hOpool : S₀own ⊆ s.pool) (_hEpool : S₀ext ⊆ s.pool)
    (_hSO : Disjoint S S₀own) (_hSE : Disjoint S S₀ext) (_hOE : Disjoint S₀own S₀ext)
    {q r : ℝ} (_hq : 0 ≤ q) (_hr : 0 ≤ r)
    (_hfin : q + r ≤ s.bank + (s.cash k + s.resv k - ∑ g ∈ s.own k, p g)
              + (∑ g ∈ S₀own, p g) + ∑ g ∈ S₀ext, p g)
    (_hself : ∑ g ∈ S₀own, p g ≤ q + r)
    (_hpure : (∀ g ∈ S₀ext, PureGood v p (insert k s.served) g) ∨
      (S = ∅ ∧ S₀own = ∅ ∧ r = 0 ∧ ∃ g0, S₀ext = {g0} ∧ q ≤ p g0))
    (_hclaim : s.req v p eps k ≤ vbarSum (v k) p S + q)
    (_hkshared : ¬ ∀ g ∈ s.ext k, PureGood v p s.served g)
    (_hkeep : ∀ g ∈ S, p g ≤ v k g)
    (_hsafenew : ∀ j, j ≠ k → (vbarSum (v j) p S + q ≤ s.req v p eps j) ∨
      (q = 0 ∧ ∀ g ∈ S, vbarSum (v j) p (S \ {g}) + p g ≤ s.req v p eps j))
    (_hcostnew : ∀ j, j ∉ insert k s.served →
      truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀own, saleLoss (v j) p (TPS n (v j) p) g ≤ 2 * GeneralTPS.thr v p j),
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))
end PhaseTPS
end FairSelling


