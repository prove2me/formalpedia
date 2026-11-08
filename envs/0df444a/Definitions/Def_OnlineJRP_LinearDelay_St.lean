-- Prove2me | Definitions.Def_OnlineJRP_LinearDelay_St
-- name    : OnlineJRP_LinearDelay_St
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:23.080195+00:00
-- url     : https://prove2.me/theorems/74ffe417-a8d6-4cf9-a180-56bfa100126f
-- title:
--   States of Algorithm 1: revealed requests, budgets, service times, purchases, plan, reference time
-- statement:
--   A state of the algorithm (at joint cost $1$) records the requests revealed so far, their **budgets** $\alpha_r$, which of them have been served and when, the purchases made, the planned purchase $(S,s)$, the current time, and the data needed for the analysis: what triggered the current call to PlanPurchase, its **reference time** $h$ (Table 1), the checkpoint $\tau^-_{\min}$ and reference time $h^-$ of the previous call, and the time and value $H$ of the most recent call to UpdateBudgets. In the initial state nothing is revealed, the plan is $(\emptyset,\infty)$ and the time is $0$.
--
--   **Formalization Note** A request is identified by its position in the list of revealed requests. The plan $(\emptyset,\infty)$ and the value $\tau^-_{\min}=\infty$ are encoded by `none`. Purchases in a state are pairs (time, items); that the items are nonempty is a consequence of the algorithm (p. 9), not a condition of the step.
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Algorithm 1, p. 4; Sec. 3.1, p. 10; Table 1, p. 11

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_OPT

namespace OnlineJRP.LinearDelay

/-- Whether the algorithm is about to call `PlanPurchase` (`call`) or waits for the next event
(`ready`). -/
inductive Phase
  | call
  | ready

/-- What triggered a call to `PlanPurchase` (Sec. 3.1, p. 10); an arrival records the value `H`
chosen by the preceding call to `UpdateBudgets`. -/
inductive Trigger
  | arrival (H : ℝ)
  | purchase

/-- A state of Algorithm 1 (Sec. 2, p. 4), at joint cost `1`.

**Formalization Note** The list position in `rev` is the identity of a request, and `α`, `svc` are
read at positions. `svc p = none` means live, `svc p = some s` means served at internal time `s`.
`plan = none` encodes the paper's `(∅, ∞)`. `ref` is the reference time `h` of the current call
(Table 1, p. 11); `lastCk` and `lastRef` are `τ⁻min` and `h⁻` of the previous call, with
`lastCk = none` encoding `τ⁻min = ∞` (p. 10); `lastUpd` is the time and the `H` of the most recent
call to `UpdateBudgets`. -/
structure St (n : ℕ) where
  /-- The requests revealed so far, a prefix of the input. -/
  rev : List (Req n)
  /-- The budgets, by position. -/
  α : ℕ → ℝ
  /-- The internal service times, by position. -/
  svc : ℕ → Option ℝ
  /-- The purchases executed so far, as pairs (time, items). -/
  bought : List (ℝ × Finset (Fin n))
  /-- The planned purchase `(S, s)`. -/
  plan : Option (Finset (Fin n) × ℝ)
  /-- The current time. -/
  now : ℝ
  phase : Phase
  trig : Option Trigger
  ref : ℝ
  lastCk : Option ℝ
  lastRef : ℝ
  lastUpd : Option (ℝ × ℝ)

/-- The initial state of Algorithm 1 (`(S, s) ← (∅, ∞)`, p. 4): nothing revealed, nothing bought,
time `0`. -/
def St.init (n : ℕ) : St n where
  rev := []
  α := fun _ => 0
  svc := fun _ => none
  bought := []
  plan := none
  now := 0
  phase := .ready
  trig := none
  ref := 0
  lastCk := none
  lastRef := 0
  lastUpd := none

end OnlineJRP.LinearDelay


