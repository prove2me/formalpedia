-- Prove2me | Definitions.Def_OnlineJRP_LinearDelay_IsRun
-- name    : OnlineJRP_LinearDelay_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:51.417704+00:00
-- url     : https://prove2.me/theorems/3455f219-84e7-4f00-b3d7-6f9a0e263d20
-- title:
--   Runs of Algorithm 1: arrival, purchase and planning steps, and $D$ along the execution
-- statement:
--   An execution of Algorithm 1 on a request sequence is a list of states starting from the initial one, with consecutive states related by one of three steps.
--
--   1. **Arrival.** From a ready state, if the next request $r^\star$ is released strictly before the planned purchase (or nothing is planned) and $H>0$ satisfies Eq. (2): reveal $r^\star$, update the budgets, record $H$. The state is then a call to PlanPurchase with reference time $h^-$ if $\tau^-_{\min}\le t+H$, and $t$ otherwise (Table 1, rows 1 and 2).
--   2. **Purchase.** From a ready state with plan $(S,s)$, with $s$ no later than the next release: serve the live requests at $S$ at time $s$. If a request stays live, the state is a call with reference time $\tau^-_{\min}$ if $\mathrm{sl}(s)=0$ and $s$ otherwise (rows 3–5); if none does, the plan is reset.
--   3. **Plan.** From a call, for $(S,s)$ returned by PlanPurchase, record the plan, the checkpoint and the reference time.
--
--   Simultaneous events are processed with planned purchases before arrivals. $D$ along the execution at time $v$ is the forecast at $v$ of the last state with current time at most $v$, and $0$ if there is none.
--
--   **Formalization Note** A call to PlanPurchase is a state before the plan step, so a statement about all calls does not assume that the plan step is possible. A run may be partial, and any admissible $H$ may occur.
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Algorithm 1, p. 4; Algorithm 2, p. 6; Table 1, p. 11; forecasts vs. execution, p. 8

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_St_Phi
import Definitions.Def_OnlineJRP_LinearDelay_St_IsPlan

namespace OnlineJRP.LinearDelay

open Finset

variable {n : ℕ}

namespace St

open Classical in
/-- The state after an arrival of `r` with the value `H` chosen in `UpdateBudgets` (Algorithm 1,
"Upon arrival of a request", p. 4, and Algorithm 2, line 4, p. 6), just before the call to
`PlanPurchase`. By Table 1 (p. 11), the reference time is `h⁻` if `τ⁻min ≤ t + H` (row 2) and `t`
otherwise (row 1, including `τ⁻min = ∞`). -/
noncomputable def afterArrive (st : St n) (c : Fin n → ℝ) (r : Req n) (H : ℝ) : St n :=
  { st.reveal r with
    α := fun p => if h : p < (st.reveal r).rev.length then st.budgetH c r H ⟨p, h⟩ else st.α p
    plan := none
    phase := .call
    trig := some (.arrival H)
    lastUpd := some (r.t, H)
    ref := if ∃ τ', st.lastCk = some τ' ∧ τ' ≤ r.t + H then st.lastRef else r.t }

open Classical in
/-- The service times after purchasing `S` at time `s`: every live revealed request at an item of `S`
is served at time `s` (Sec. 1, p. 1). -/
noncomputable def serve (st : St n) (S : Finset (Fin n)) (s : ℝ) : ℕ → Option ℝ := fun p =>
  if h : p < st.rev.length then
    if st.svc p = none ∧ (st.rev.get ⟨p, h⟩).i ∈ S then some s else st.svc p
  else st.svc p

/-- The state right after executing the purchase `(S, s)`, with the budgets unchanged. -/
noncomputable def purchased (st : St n) (S : Finset (Fin n)) (s : ℝ) : St n :=
  { st with
    svc := st.serve S s
    bought := st.bought ++ [(s, S)]
    now := s
    plan := none }

open Classical in
/-- The state after reaching time `s` of the planned purchase (Algorithm 1, p. 4). If live requests
remain the algorithm is about to call `PlanPurchase`, with reference time by Table 1 (p. 11):
`τ⁻min` if `sl(t) = 0` (rows 3, 4) and `t` otherwise (row 5). If none remains the plan is reset to
`(∅, ∞)`, and `τ⁻min = ∞` for the next arrival (p. 10).

**Formalization Note** The value `sl(t) < 0` is unreachable, since the purchase is affordable; row 5
of Table 1 reads `sl(t) > 0`, and the `else` branch covers it. `lastCk` is `some` at every purchase,
so the default of `getD` is never read. -/
noncomputable def afterBuy (st : St n) (x : ℝ) (c : Fin n → ℝ) (S : Finset (Fin n)) (s : ℝ) : St n :=
  if (st.purchased S s).live.Nonempty then
    { st.purchased S s with
      phase := .call
      trig := some .purchase
      ref := if (st.purchased S s).sl x c s = 0 then st.lastCk.getD s else s }
  else
    { st.purchased S s with
      phase := .ready
      lastCk := none }

/-- The state after `PlanPurchase` returned `(S, s)`: the call's checkpoint and reference time are
recorded for the next call as `τ⁻min` and `h⁻` (p. 10). -/
noncomputable def afterPlan (st : St n) (S : Finset (Fin n)) (s : ℝ) : St n :=
  { st with
    plan := some (S, s)
    phase := .ready
    lastCk := some st.τmin
    lastRef := st.ref }

end St

/-- An arrival event with value `H` (Algorithm 1, p. 4; Algorithm 2, line 3, p. 6): the next request
`r` of the input is due before the planned purchase, strictly since simultaneous events are processed
with planned purchases before arrivals (p. 4), and `H > 0` satisfies Eq. (2).

**Formalization Note** Any admissible `H` may be chosen ("Choose any `H > 0`"), so the milestones hold
for every such choice. -/
def ArrivalStep (c : Fin n → ℝ) (σ : List (Req n)) (st : St n) (H : ℝ) (st' : St n) : Prop :=
  st.phase = .ready ∧ ∃ r, σ[st.rev.length]? = some r ∧
    (∀ S s, st.plan = some (S, s) → r.t < s) ∧ 0 < H ∧ st.Phi c r H = 1 ∧
    st' = st.afterArrive c r H

/-- A purchase event (Algorithm 1, p. 4): time `s` of the planned purchase is reached, no later than
the next arrival (planned purchases are processed before arrivals, p. 4). -/
def BuyStep (x : ℝ) (c : Fin n → ℝ) (σ : List (Req n)) (st : St n) (S : Finset (Fin n)) (s : ℝ)
    (st' : St n) : Prop :=
  st.phase = .ready ∧ st.plan = some (S, s) ∧
    (∀ r, σ[st.rev.length]? = some r → s ≤ r.t) ∧ st' = st.afterBuy x c S s

/-- A call to `PlanPurchase` returning `(S, s)`. -/
def PlanStep (x : ℝ) (c : Fin n → ℝ) (st : St n) (S : Finset (Fin n)) (s : ℝ) (st' : St n) : Prop :=
  st.phase = .call ∧ st.IsPlan x c S s ∧ st' = st.afterPlan S s

/-- One step of Algorithm 1 on the input `σ`, at joint cost `1`. -/
def Step (x : ℝ) (c : Fin n → ℝ) (σ : List (Req n)) (st st' : St n) : Prop :=
  (∃ H, ArrivalStep c σ st H st') ∨ (∃ S s, BuyStep x c σ st S s st') ∨
    (∃ S s, PlanStep x c st S s st')

/-- `l` is a (possibly partial) execution of Algorithm 1 on the input `σ`, from the initial state.

**Formalization Note** A "call to `PlanPurchase`" is a state of `l` with `phase = .call`, *before* the
plan step: the statements about calls do not assume that line 4 of Algorithm 3 finds a time `s`. -/
def IsRun (x : ℝ) (c : Fin n → ℝ) (σ : List (Req n)) (l : List (St n)) : Prop :=
  l.head? = some (St.init n) ∧ l.IsChain (Step x c σ)

/-- `D(v)` along the actual execution `l` (p. 8 distinguishes it from a forecast): the forecast at `v`
of the last state of `l` with `now ≤ v`, and `0` if there is none. -/
noncomputable def execD (l : List (St n)) (v : ℝ) : ℝ :=
  match (l.filter fun st => st.now ≤ v).getLast? with
  | some st => st.D v
  | none => 0

end OnlineJRP.LinearDelay


