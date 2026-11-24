-- Prove2me | Definitions.Def_ReedGGN_Regulator_Supplement_FCFS
-- name    : ReedGGN_Regulator_Supplement_FCFS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:02:36.167568+00:00
-- url     : https://prove2.me/theorems/5a0cfffd-732a-42ec-9dd2-e960b0f779ea
-- title:
--   §2 — The finite-server FCFS service-entry rule
-- statement:
--   For a published queue sample path with $N\ge1$ servers, list the initial waiting customers before subsequent arrivals, in arrival order. A customer's ready time is zero for an initial waiter and the arrival time otherwise. Start each fresh service at
--
--   $$e_j=\max\{\text{ready}_j,\min_{1\le s\le N}\text{available}_{j,s}\}.$$
--
--   The chosen earliest available server next becomes available at $e_j+\eta_j$; other servers keep their availability. Initially occupied servers have the given residual availability and idle servers have availability zero. The published non-idling predicate is retained as its count invariant. Zero services, initial residual atoms and tied arrivals are admitted. This gives an actual FCFS evolution driven by primitive data, rather than arbitrary waiting functions or an assumed queue identity.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, §2, pp.6–8

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_NonIdling

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

open ReedGGN.SystemEq

/-- Entry time of fresh-service customer j+1, including the initial waiting customers first.
 The remaining customers are ordered by arrival index, including ties at time zero. -/
def entry (p : SamplePath) (j : ℕ) : ℝ :=
  if j < p.Q₀ - p.N then p.wt (j + 1)
  else p.τ (j + 1 - (p.Q₀ - p.N)) + p.w (j + 1 - (p.Q₀ - p.N))

/-- Earliest time fresh customer j+1 is present: initial waiters are present at 0−. -/
def ready (p : SamplePath) (j : ℕ) : ℝ :=
  if j < p.Q₀ - p.N then 0 else p.τ (j + 1 - (p.Q₀ - p.N))

/-- An actual N-server non-idling FCFS schedule. Initial server availability consists of the
 initial residuals and zero for idle servers. In customer order, choose an earliest available
 server, start at max(arrival, availability), and update just that server. This is the primitive
 scheduling rule, not the desired system equation or any limit theorem. Zero services and
 simultaneous arrivals are admitted. Ties use any minimising server and preserve customer order. -/
def IsFCFS (p : SamplePath) : Prop :=
  0 < p.N ∧ (∀ i, 0 ≤ p.ηt i) ∧ (∀ i, 0 ≤ p.η i) ∧ NonIdling p ∧
  ∃ (server : ℕ → Fin p.N) (available : ℕ → Fin p.N → ℝ),
    (∀ s, available 0 s = if s.val < min p.Q₀ p.N then p.ηt (s.val + 1) else 0) ∧
    (∀ j s, available j (server j) ≤ available j s) ∧
    (∀ j, entry p j = max (ready p j) (available j (server j))) ∧
    (∀ j s, available (j + 1) s =
      if s = server j then entry p j + p.η (j + 1) else available j s)

end ReedGGN.Regulator.Supplement


