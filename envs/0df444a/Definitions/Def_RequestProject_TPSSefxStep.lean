-- Prove2me | Definitions.Def_RequestProject_TPSSefxStep
-- name    : RequestProject_TPSSefxStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:18:49.574112+00:00
-- url     : https://prove2.me/theorems/1b6b33fe-fd53-4506-b41f-f8a532bcc801
-- title:
--   TPSSefx Step
-- statement:
--   Definitions and structural lemmas for TPSSefx Step, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
section Req
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end Req
section Feas
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end Feas
section Package
variable (v : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)
end Package
section CaseA
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
end CaseA
section Steal
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
def CStealStep (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) : Prop :=
  ∀ (s : CStage G n) (k0 : Fin n), s.Good v p eps → k0 ∉ s.served →
    ∀ S S₀ : Finset G, S ∪ S₀ ⊆ s.pool → Disjoint S S₀ →
      CfgTPS.Adm v p (s.req v p eps) k0 s.bank S S₀ →
      (∀ T T₀ : Finset G, T ∪ T₀ ⊆ s.pool → Disjoint T T₀ →
        CfgTPS.Adm v p (s.req v p eps) k0 s.bank T T₀ →
        (S ∪ S₀).card * (s.pool.card + 1) + S₀.card
          ≤ (T ∪ T₀).card * (s.pool.card + 1) + T₀.card) →
      ∀ k : Fin n, k ∈ s.served →
        s.req v p eps k ≤ vbarSum (v k) p S + CfgTPS.Qc v p (s.req v p eps) k0 S →
        ∃ s' : CStage G n, s'.Good v p eps ∧
          (s.served.card < s'.served.card ∨
            (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p))
end Steal
end ChargeTPS
end FairSelling


