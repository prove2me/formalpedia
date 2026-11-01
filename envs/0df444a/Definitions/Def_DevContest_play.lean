-- Prove2me | Definitions.Def_DevContest_play
-- name    : DevContest_play
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:04.247317+00:00
-- url     : https://prove2.me/theorems/c77352b0-d16f-4bc4-b1c2-7c34326f155e
-- title:
--   The realized contest: integrated hazards, hitting times and outcomes
-- statement:
--   Given a strategy profile $x$, a draw $u$ and clocks $e$, the contest is played as follows. A stage of agent $i$ begun at date $s$ is completed at the first date $t\ge s$ at which $\int_s^t\lambda x^i_\tau\,d\tau$ reaches the clock of that stage. Thus a success arrives with instantaneous probability $\lambda x^i$.
--
--   1. In **state 00** both agents run on the empty record, until the first arrival, at $t_1$, by the leader.
--   2. In **state 10** the record contains the leader's success. Her second-stage clock starts, and the laggard keeps the hazard she has accumulated. The state lasts until the leader completes, which ends the contest, or until the laggard arrives at $t_2$.
--   3. In **state 11** the record contains both successes. The laggard's second-stage clock starts, and the leader keeps her accumulated hazard. The first completion ends the contest.
--
--   The outcome is the final record, the end date $T\in[0,\infty]$, and the winner, if any: the first agent with two successes. This is the contest of §3 with a fixed reward.
--
--   **Formalization Note** An event that never occurs has date $\infty$. Ties have probability zero, because integrated hazards are continuous; the tie rule is that agent $0$ leads at equal first arrivals and the leader wins a tie with any event of the laggard.
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, §3, p.10

import Mathlib
import Definitions.Def_DevContest_Policy

open scoped ENNReal NNReal
open MeasureTheory

namespace DevContest

/-- The integrated hazard `∫_s^t λ f(τ) dτ` of an effort path `f`, Khorasani, Körpeoğlu, Krishnan,
*Dynamic Development Contests*, author manuscript, §3, p.10.

**Formalization Note.** Mathlib has no Lebesgue measure on `ℝ≥0`, so the integral runs over the real
interval `[s,t)` and `f` is read at `τ.toNNReal`. The integral is a `lintegral`, so it is never a
junk value. -/
noncomputable def hazard (lam : ℝ) (f : ℝ≥0 → ℝ) (s t : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal lam * ∫⁻ τ in Set.Ico (s : ℝ) (t : ℝ), ENNReal.ofReal (f τ.toNNReal)

/-- The first date `t ≥ s` at which the integrated hazard `H` reaches the clock value `e`, and `⊤` if
it never does. -/
noncomputable def hitTime (H : ℝ≥0 → ℝ≥0∞) (s : ℝ≥0) (e : ℝ≥0∞) : ℝ≥0∞ :=
  sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | s ≤ t ∧ e ≤ H t})

/-- The realized outcome of a contest: the record `first` of first successes, the end date `lead`
(the paper's `T`, §3, p.10), and the `winner`; `lead = ⊤` and `winner = none` when it never ends. -/
structure Outcome where
  /-- The realized first-success dates. -/
  first : Rec
  /-- The date at which the contest ends. -/
  lead : ℝ≥0∞
  /-- The agent who gets the reward, if the contest ends. -/
  winner : Option (Fin 2)

/-- The contest played by the profile `x` on randomization `u` and clocks `e`, §3, p.10: each stage
of agent `i` ends when her integrated hazard reaches her clock, and the first agent with two
successes ends the contest and wins. The play goes through three states.

* State `00`: both agents run on the empty record, until the first arrival `t1` by the leader `l`.
* State `10`: the record has `l ↦ t1`. The leader's second-stage clock starts; the laggard `g` keeps
  the hazard she has accumulated. It lasts until the leader completes, or the laggard arrives at
  `t2`.
* State `11`: the record has both. The laggard's second-stage clock starts, the leader keeps her
  accumulated hazard, and the first completion ends the contest.

**Formalization Note.** If an event never occurs its date is `⊤`. Tie rule (ties have probability
zero, because the integrated hazards are continuous): at equal first arrivals agent `0` leads and
agent `1` arrives immediately after, in state `10`; the leader wins a tie between her completion
and any event of the laggard. -/
noncomputable def play (lam : ℝ) {U : Type} (x : Fin 2 → Strategy U) (u : U) (e : Clocks) :
    Outcome :=
  let a : Fin 2 → ℝ≥0∞ := fun i =>
    hitTime (hazard lam (fun τ => x i τ noRec u) 0) 0 (ENNReal.ofReal (e (i, 0)))
  let l : Fin 2 := if a 0 ≤ a 1 then 0 else 1
  let g : Fin 2 := rival l
  if a l = ⊤ then ⟨noRec, ⊤, none⟩ else
  let t1 : ℝ≥0 := (a l).toNNReal
  let r1 : Rec := Function.update noRec l (t1 : ℝ≥0∞)
  let Hg : ℝ≥0 → ℝ≥0∞ := fun t =>
    hazard lam (fun τ => x g τ noRec u) 0 t1 + hazard lam (fun τ => x g τ r1 u) t1 t
  let Hl : ℝ≥0 → ℝ≥0∞ := hazard lam (fun τ => x l τ r1 u) t1
  let b : ℝ≥0∞ := hitTime Hg t1 (ENNReal.ofReal (e (g, 0)))
  let d : ℝ≥0∞ := hitTime Hl t1 (ENNReal.ofReal (e (l, 1)))
  if d ≤ b then
    (if d = ⊤ then ⟨r1, ⊤, none⟩ else ⟨r1, d, some l⟩)
  else
    let t2 : ℝ≥0 := b.toNNReal
    let r2 : Rec := Function.update r1 g (t2 : ℝ≥0∞)
    let Ll : ℝ≥0 → ℝ≥0∞ := fun t => Hl t2 + hazard lam (fun τ => x l τ r2 u) t2 t
    let Lg : ℝ≥0 → ℝ≥0∞ := hazard lam (fun τ => x g τ r2 u) t2
    let d1 : ℝ≥0∞ := hitTime Ll t2 (ENNReal.ofReal (e (l, 1)))
    let d2 : ℝ≥0∞ := hitTime Lg t2 (ENNReal.ofReal (e (g, 1)))
    if d1 ≤ d2 then
      (if d1 = ⊤ then ⟨r2, ⊤, none⟩ else ⟨r2, d1, some l⟩)
    else
      ⟨r2, d2, some g⟩

end DevContest


