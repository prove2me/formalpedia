-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Supplement_Sequential
-- name    : StrategicRFx_Benefit_Supplement_Sequential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:05:43.692861+00:00
-- url     : https://prove2.me/theorems/c4a56754-eb49-4c7c-ae9f-5df3452fc38b
-- title:
--   §2.3.2 — contract-level follower correspondence and sequential bargaining without RFx
-- statement:
--   For either choice of leader, the follower observes the leader's contract and solves the appropriate simultaneous-bargaining program. His continuation is a correspondence of attained solutions, including the continuation after no deal with the leader. The leader maximizes
--
--   $$\pi_i^{\theta_i}(\pi_0-\pi_0^{\mathrm{failure}})^{1-\theta_i}$$
--
--   subject to individual rationality, accounting for the follower's continuation. Both dual and exclusive sourcing and the case where both bargaining programs are infeasible are represented. Actual sourcing remains the buyer's optimum.
--
--   This definition formalizes §2.3.2 before quotations are introduced. It is infrastructure, and does not fulfill Theorem 2, which also covers accepted and rejected RFx quotations. A contract without an attained follower continuation is not assigned a numerical fallback payoff. No total or uniquely selected continuation is assumed.
--
--   **Formalization Note** Every consistent selection is admitted. It selects only where an attained follower response exists; it does not assert universal attainment. The same policy evaluates candidate contracts and the no-deal fallback. The leader no longer maximizes over a union of different follower selections.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), §2.3.2, pp. 9–10 (without RFx)

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Simultaneous

namespace StrategicRFx.Benefit.Supplement

/-- One supplier's three [Simu] cases, with an externally specified buyer
reservation payoff. The follower uses these cases after observing the leader. -/
def SupplierBargainAt (M : Technology) (i : Fin 2) (x : ContractOutcome) (D : ℝ) : Prop :=
  match x.order with
  | .dual q => IsDualBargain M i (x.contracts (other i)) (x.contracts i) q D
  | .single k q => if k = i then IsSingleBargain M i (x.contracts i) (.single i q) D
      else NoBargainFeasible M i (x.contracts (other i)) D
  | .none => NoBargainFeasible M i (x.contracts (other i)) D

/-- §2.3.2's multiple-valued follower continuation, before any RFx stage.
It is a correspondence, not a total choice function on all transfer functions.
The no-deal continuation is obtained by passing `none`. -/
def FollowerContinuation (M : Technology) (leader : Fin 2) (d : Contract)
    (x : ContractOutcome) : Prop :=
  ValidOutcome M x ∧ x.contracts leader = d ∧
    SupplierBargainAt M (other leader) x
      (exclusivePayoff M d leader (x.exclusiveOrder leader)).buyer

/-- A consistent selection from the possibly multivalued follower response.
It selects only attained responses and is required only where a response
exists; no arbitrary transfer function is assumed to attain a maximum. -/
def FollowerPolicy (M : Technology) (leader : Fin 2)
    (F : Contract → ContractOutcome → Prop) : Prop :=
  (∀ d x, F d x → FollowerContinuation M leader d x) ∧
  (∀ d, (∃ x, FollowerContinuation M leader d x) → ∃ x, F d x) ∧
  (∀ d x y, F d x → F d y → x = y)

/-- A feasible agreement in [Sequ-i] or [Sequ-i′], evaluated using the
same follower selection at every candidate leader contract and no deal. -/
def SequentialCandidate (M : Technology) (i : Fin 2)
    (F : Contract → ContractOutcome → Prop) (D : ℝ)
    (dual : Bool) (x : ContractOutcome) : Prop :=
  F (x.contracts i) x ∧
  (if dual then ∃ q, x.order = .dual q else ∃ q, x.order = .single i q) ∧
  0 ≤ (x.payoff M).supplier i ∧ D ≤ (x.payoff M).buyer

/-- §2.3.2 for either leader. The existentially quantified policy lets the
source's multivalued follower choose any consistent response; maximizing
over the union of different selections is not required of the leader.
Policies never assume coordination or cost-plus implementation. -/
def IsSequentialWithoutRFx (M : Technology) (i : Fin 2) (x : ContractOutcome) : Prop :=
  ∃ F, FollowerPolicy M i F ∧ ∃ z, F none z ∧ F (x.contracts i) x ∧
    let D := (z.payoff M).buyer
    ((∃ dual, SequentialCandidate M i F D dual x ∧
      ∀ y, SequentialCandidate M i F D dual y →
        nashProduct (M.power i) ((y.payoff M).supplier i) ((y.payoff M).buyer - D) ≤
        nashProduct (M.power i) ((x.payoff M).supplier i) ((x.payoff M).buyer - D)) ∨
     ((¬ ∃ dual y, SequentialCandidate M i F D dual y) ∧
       (x.order = .none ∨ ∃ q, x.order = .single (other i) q) ∧ (x.payoff M).buyer = D))

end StrategicRFx.Benefit.Supplement


