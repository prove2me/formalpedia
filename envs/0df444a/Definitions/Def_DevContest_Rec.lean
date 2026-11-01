-- Prove2me | Definitions.Def_DevContest_Rec
-- name    : DevContest_Rec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:35.891042+00:00
-- url     : https://prove2.me/theorems/6783c67b-119a-473d-a2d2-e7b793675501
-- title:
--   Records of first successes, opponents and stage clocks of the two-agent, two-stage contest
-- statement:
--   There are two agents and two stages, and time runs continuously over an infinite horizon. A **record** $r=(r_0,r_1)$ lists the dates of the agents' first successes, with values in $[0,\infty]$, where $r_i=\infty$ means that agent $i$ has no first success yet. The record as it stands at time $t$ keeps the entries dated at most $t$ and replaces the others by $\infty$. The opponent of agent $i$ is written $-i$.
--
--   The arrival randomness consists of four **clocks** $e_{i,j}$, one for each agent $i$ and stage $j$.
--
--   These objects carry the whole model: a contest is determined by the records it passes through.
--
--   **Formalization Note** Agents are `Fin 2`, time is `ℝ≥0`, and "no success yet" is `⊤ : ℝ≥0∞`.
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, §3, p.10

import Mathlib

open scoped ENNReal NNReal

namespace DevContest

/-- The record of first successes in the two-agent, two-stage contest of Khorasani, Körpeoğlu,
Krishnan, *Dynamic Development Contests*, author manuscript, §3, p.10: `r i` is the date of agent
`i`'s first success.

**Formalization Note.** The agents are `Fin 2`, time is `ℝ≥0`, and `⊤ : ℝ≥0∞` means "no success
yet". -/
abbrev Rec : Type := Fin 2 → ℝ≥0∞

/-- The empty record: neither agent has a success. -/
def noRec : Rec := fun _ => ⊤

/-- The record as it stands at time `t`: a first success dated after `t` has not happened yet. -/
noncomputable def trunc (t : ℝ≥0) (r : Rec) : Rec := fun i => if r i ≤ (t : ℝ≥0∞) then r i else ⊤

/-- The opponent `-i` of agent `i`. -/
def rival (i : Fin 2) : Fin 2 := i + 1

/-- The arrival randomness of the contest. Clock `(i, j)` is agent `i`'s clock for stage `j`
(`j = 0` is the first stage).

**Formalization Note.** The paper's Poisson arrival with instantaneous probability `λ x` (§3, p.10)
is represented by a unit-exponential clock: stage `j` of agent `i` is completed when `∫ λ x`, taken
over the time she spends in that stage, reaches the clock. -/
abbrev Clocks : Type := Fin 2 × Fin 2 → ℝ

end DevContest


