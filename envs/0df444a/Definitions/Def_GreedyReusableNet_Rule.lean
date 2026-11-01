-- Prove2me | Definitions.Def_GreedyReusableNet_Rule
-- name    : GreedyReusableNet_Rule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:02.596526+00:00
-- url     : https://prove2.me/theorems/d67114a9-f273-4ca2-af35-ef9cb643e75e
-- title:
--   Online policy (decision rule with randomization)
-- statement:
--   An **online policy** draws an initial seed $s$ from a law $\mu$ once, before the first period, and in period $t$ proposes an action set as a function of $s$, $t$, its history and a fresh uniform period seed. The paper: "The policy taken by the DM at time $t$ is a mapping from all the information available by time $t$ to an action set $\mathcal A^\pi_t\in\mathscr A_t$. The policy is allowed to be randomizing over all available action sets according to some probability distribution that is adapted to the currently available information."
--
--   A policy is chosen for a given instance and may use all of it (the benchmark is clairvoyant about the instance); it does not see future seeds. GRD-R's random threshold is its initial seed.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, pp.8–9; §2.3, p.15

import Mathlib
import Definitions.Def_GreedyReusableNet_History

open MeasureTheory

namespace GreedyReusableNet

/-- **An online policy** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1, pp.8–9: "The policy
taken by the DM at time `t` is a mapping from all the information available by time `t` to an
action set `𝒜^π_t ∈ 𝒜_t`. The policy is allowed to be randomizing over all available action sets
according to some probability distribution that is adapted to the currently available
information.").

A policy draws an initial seed `s ∼ seedLaw` once, before the first period, and in period `t`
proposes the action set `act s t h u` from its history `h` and a fresh period seed `u` (uniform
on `[0, 1]`, from the tape). The process takes the proposal if it is an available action set of
`𝒜_t` and the empty action set otherwise (`takenAction`).

**Formalization Note** A policy is chosen for a fixed instance, so it may use the whole instance
(the benchmark is "clairvoyant … complete knowledge of `𝓘`", p.15); it does not see future
seeds. GRD-R's random threshold is its initial seed. Measurability and `seedLaw` being a
probability measure are required separately (`IsAdmissible`). -/
structure Rule (N : ℕ) where
  /-- the law of the initial seed, drawn once before period `0` -/
  seedLaw : Measure ℝ
  /-- the decision rule: initial seed, period, history, period seed ↦ proposed action set -/
  act : ℝ → ℕ → History N → ℝ → Finset (Finset (Fin N))

end GreedyReusableNet


