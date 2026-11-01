-- Prove2me | Definitions.Def_DevContest_leaderRace
-- name    : DevContest_leaderRace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:53:30.260991+00:00
-- url     : https://prove2.me/theorems/78a8a7c7-36b2-4e61-9bf9-4d4c364c41f9
-- title:
--   The contest restarted after a first success: continuation payoffs and durations
-- statement:
--   These are the continuation objects of pp.ec18–ec19, as expectations over three independent unit-exponential clocks.
--
--   1. A **leader race** from date $s$: the leader has just obtained her first success and exerts full effort until the end; the laggard exerts a deterministic effort $y$ until she arrives, after which both exert full effort.
--   2. A **both race** from date $s$: both agents are in the second stage and both exert full effort.
--
--   For an agent exerting full effort, the **continuation payoff** from $s$ is $\mathbb E[\bar R\,1\{\text{she wins}\}-c\,(T-s)]$, and the **duration** is $\mathbb E[T-s]$. This defines $V_{1,0}$ and $T_{1,0}$ (leader race) and $V_{1,1}$ (both race). Under PCSD the continuation payoff upon a first success at $t$ is
--   $$
--   V^\phi_{1,t}=p_tV_{1,1}+(1-p_t)\bigl(\phi^*_t\,V_{1,0}[y\equiv0]+(1-\phi^*_t)\,V_{1,0}[y\equiv1]\bigr).
--   $$
--
--   **Formalization Note** Arrivals are memoryless, so the laggard's clock restarts at $s$. In both races $T\le s+e_0/\lambda$, so all the expectations are finite.
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, pp.ec18–ec19, displays (EC.41)–(EC.42)

import Mathlib
import Definitions.Def_DevContest_play
import Definitions.Def_DevContest_pcsdBelief

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace DevContest

/-- The law of the three unit-exponential clocks of a contest restarted after a first success. -/
noncomputable def raceLaw : Measure (Fin 3 → ℝ) := Measure.pi fun _ => expMeasure 1

/-- The contest from the date `s` at which the leader has just obtained her first success and her
rival is still in the first stage, Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*,
author manuscript, pp.ec18–ec19. The leader exerts full effort, the laggard exerts the deterministic
effort `y` until she catches up, and both exert full effort after a catch-up. Clock `0` is the
leader's second stage, clock `1` the laggard's first stage, clock `2` the laggard's second stage.
The value is the end date together with whether the leader wins.

**Formalization Note.** Arrivals are memoryless, so the laggard's clock restarts at `s`. -/
noncomputable def leaderRace (lam : ℝ) (y : ℝ≥0 → ℝ) (s : ℝ≥0) (e : Fin 3 → ℝ) : ℝ≥0∞ × Bool :=
  let d : ℝ≥0∞ := hitTime (hazard lam (fun _ => 1) s) s (ENNReal.ofReal (e 0))
  let b : ℝ≥0∞ := hitTime (hazard lam y s) s (ENNReal.ofReal (e 1))
  if d ≤ b then (d, true) else
    let t2 : ℝ≥0 := b.toNNReal
    let d2 : ℝ≥0∞ := hitTime (hazard lam (fun _ => 1) t2) t2 (ENNReal.ofReal (e 2))
    if d ≤ d2 then (d, true) else (d2, false)

/-- The contest from the date `s` with both agents in the second stage and both exerting full effort:
the end date, and whether the agent of clock `0` wins. -/
noncomputable def bothRace (lam : ℝ) (s : ℝ≥0) (e : Fin 3 → ℝ) : ℝ≥0∞ × Bool :=
  let d : ℝ≥0∞ := hitTime (hazard lam (fun _ => 1) s) s (ENNReal.ofReal (e 0))
  let d2 : ℝ≥0∞ := hitTime (hazard lam (fun _ => 1) s) s (ENNReal.ofReal (e 2))
  if d ≤ d2 then (d, true) else (d2, false)

/-- The expected continuation payoff from `s` of an agent exerting full effort until the end: reward
`Rbar` if she wins, minus `c` per unit of time.

**Formalization Note.** In both races the end date is at most the finite date `s + e 0 / λ`, whose
expectation is finite, so the Bochner integral is not a junk value. -/
noncomputable def raceValue (c Rbar : ℝ) (s : ℝ≥0) (o : (Fin 3 → ℝ) → ℝ≥0∞ × Bool) : ℝ :=
  ∫ e, ((if (o e).2 then Rbar else 0) - c * ((o e).1.toReal - s)) ∂raceLaw

/-- The expected time from `s` to the end of a race. -/
noncomputable def raceDuration (s : ℝ≥0) (o : (Fin 3 → ℝ) → ℝ≥0∞ × Bool) : ℝ :=
  ∫ e, ((o e).1.toReal - s) ∂raceLaw

/-- `V_{1,0}`: the continuation payoff of a leader whose rival, in the first stage, exerts `y`. -/
noncomputable def leaderValue (lam c Rbar : ℝ) (y : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  raceValue c Rbar s (leaderRace lam y s)

/-- `T_{1,0}`: the expected time from the leader's first success to the end of the contest. -/
noncomputable def leaderDuration (lam : ℝ) (y : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  raceDuration s (leaderRace lam y s)

/-- `V_{1,1}`: the continuation payoff of an agent when both are in the second stage. -/
noncomputable def bothValue (lam c Rbar : ℝ) (s : ℝ≥0) : ℝ :=
  raceValue c Rbar s (bothRace lam s)

/-- `V^φ_{1,p}`, display (EC.41), p.ec18: the continuation payoff upon a first success at `t` under
PCSD. With probability `p_t` the rival has already succeeded; otherwise this success is disclosed
with probability `φ*_t` and the rival quits, and it is not disclosed with probability `1 - φ*_t` and
the rival keeps working. -/
noncomputable def pcsdContinuation (lam c Rbar : ℝ) (t : ℝ≥0) : ℝ :=
  pcsdBelief lam c Rbar t * bothValue lam c Rbar t +
    (1 - pcsdBelief lam c Rbar t) *
      (phiStar lam c Rbar t * leaderValue lam c Rbar (fun _ => 0) t +
        (1 - phiStar lam c Rbar t) * leaderValue lam c Rbar (fun _ => 1) t)

end DevContest


