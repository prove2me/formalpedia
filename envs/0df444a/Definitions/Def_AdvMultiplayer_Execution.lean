-- Prove2me | Definitions.Def_AdvMultiplayer_Execution
-- name    : AdvMultiplayer_Execution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:09:45.270649+00:00
-- url     : https://prove2.me/theorems/cccf5811-46e2-4959-a2e1-af1f0169c807
-- title:
--   Joint executions and their cost
-- statement:
--   A round of an execution computes all arms from the players' own states, then the observations by (1), then every local update. The module defines the state after each round, the record of each round, and the total number of ticks over the $T$ rounds. A flag selects the reference execution of Algorithm 8: it fixes $J$, tests only the true row, rejects every decoded word other than the one currently encoded on its channel, and at launch puts every follower outside the true-$J$ unoccupied state into it.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 1.1; Algorithm 8, p.44; Section 8

import Mathlib
import Definitions.Def_AdvMultiplayer_protocol

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- The local states of all players. -/
abbrev Joint := Fin p.m → Local p

/-- The coordinator's label. -/
def coordinator : Fin p.m := ⟨0, by have := p.two_le_m; omega⟩

/-- The word currently encoded on a channel at arm choice (p.20, App. A.2), from the states `mid`
after arm choice: on DOWN to follower `i`, the coordinator's record while `i ∈ P`; on UP from `i`, an
activated unoccupied follower's offer (32). -/
def curWord (mid : Joint p) (dir : Bool) (i : ℕ) : Option (Word p) :=
  if dir then
    if h : i < p.m then
      (if (mid ⟨i, h⟩).activated ∧ (mid ⟨i, h⟩).fol.state = 0 then
        some (encUp p ⟨(mid ⟨i, h⟩).fol.rc.σ, (mid ⟨i, h⟩).fol.S, (mid ⟨i, h⟩).fol.δ,
          (mid ⟨i, h⟩).fol.b⟩)
      else none)
    else none
  else
    let c := mid (coordinator p)
    if c.activated ∧ c.co.σ > 0 ∧ c.co.P i = true then some (encDown p (c.co.msg i)) else none

/-- The record of one round of an execution: the states at round start, after arm choice and after
the round; arms, true observations and the rounded ones; the local reports; and the followers
corrected at launch. -/
structure RoundRec where
  pre : Joint p
  mid : Joint p
  post : Joint p
  arms : Fin p.m → Fin p.K
  labels : Fin p.m → ℕ
  obs : Fin p.m → ℝ
  logs : Fin p.m → Log p
  corrected : Fin p.m → Bool

/-- The launch correction of Algorithm 8, lines 7–9: after the block end that launches, every
follower outside the true-`J` unoccupied state is put in it. -/
def correct (j : ℕ) (i : Fin p.m) (s : Local p) : Local p × Bool :=
  if i = coordinator p ∨ (s.activated ∧ s.row = j) then (s, false)
  else ({ Local.init p with activated := true, row := j }, true)

/-- **One round of an execution.** Gan, arXiv:2610.05688, Section 1.1 and Algorithms 6–8: all players
choose their arms from their own states, (1) gives the observations, and every player updates its own
state. In a reference execution the current words are passed to the filter, and the launch correction
is applied.

**Formalization Note.** `kd = RunKind.actual` is the execution of `protocol`; `⟨some j, false⟩` is the
same with `J = j`; `⟨some j, true⟩` is the reference execution of Algorithm 8 and Section 4 (p.20). -/
noncomputable def jointStep (d : TableData p) (kd : RunKind) (r : Rewards p) (ω : Tapes p) (t : ℕ)
    (st : Joint p) : StateM ℕ (RoundRec p) := do
  let ch ← fillProg fun i : Fin p.m =>
    chooseProg p d kd i.val t (tapeAt p (ω i) t) (st i)
  let mid : Joint p := fun i => (ch i).2
  let arms : Fin p.m → Fin p.K := fun i => armOf p (ch i).1
  let y := payoff p r t arms
  let md : Mode p := ⟨kd, curWord p mid⟩
  let fin ← fillProg fun i : Fin p.m => finishProg p d md i.val t (ch i).1 (y i) (mid i)
  let after : Joint p := fun i => (fin i).1
  let launch : Bool := kd.reference && !(st (coordinator p)).activated &&
    (after (coordinator p)).activated
  let j := kd.forceRow.getD 0
  let post : Joint p := fun i => if launch then (correct p j i (after i)).1 else after i
  let cor : Fin p.m → Bool := fun i => launch && (correct p j i (after i)).2
  pure ⟨st, mid, post, arms, fun i => (ch i).1, y, fun i => (fin i).2, cor⟩

/-- The joint state after `n` rounds. -/
noncomputable def stateAfter (d : TableData p) (kd : RunKind) (r : Rewards p) (ω : Tapes p) :
    ℕ → Joint p
  | 0 => fun _ => Local.init p
  | n + 1 => ((jointStep p d kd r ω (n + 1) (stateAfter d kd r ω n)).run' 0).post

/-- The record of round `t`. -/
noncomputable def roundAt (d : TableData p) (kd : RunKind) (r : Rewards p) (ω : Tapes p) (t : ℕ) :
    RoundRec p :=
  (jointStep p d kd r ω t (stateAfter p d kd r ω (t - 1))).run' 0

/-- The ticks of the whole execution over the `T` rounds, all players together. The programs never
read the counter, so each round may be run from `0`. -/
noncomputable def execTicks (d : TableData p) (kd : RunKind) (r : Rewards p) (ω : Tapes p) : ℕ :=
  ∑ t ∈ Finset.Icc 1 p.T,
    ((jointStep p d kd r ω t (stateAfter p d kd r ω (t - 1))).run 0).2

/-- **Total operations of the strategy.** Gan, arXiv:2610.05688, Section 8: the ticks of the actual
execution on the construction data, and one tick per player and round for the fixed-arm fallback. -/
noncomputable def playTicks (tab : Table p) (r : Rewards p) (ω : Tapes p) : ℕ :=
  match tab with
  | Sum.inl _ => p.m * p.T
  | Sum.inr d => if p.branch then execTicks p d RunKind.actual r ω else p.m * p.T

end AdvMultiplayer


