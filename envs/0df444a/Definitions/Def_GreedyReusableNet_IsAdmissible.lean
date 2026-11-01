-- Prove2me | Definitions.Def_GreedyReusableNet_IsAdmissible
-- name    : GreedyReusableNet_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:38.709625+00:00
-- url     : https://prove2.me/theorems/45c6f93e-f369-497b-a17a-8dc25b7a5dd0
-- title:
--   Admissible online policies
-- statement:
--   A policy is **admissible** if its initial seed is drawn from a probability measure and, for every period and history, its proposed action set is a measurable function of the initial seed and the period seed. The benchmark OPT ranges over the admissible policies.
--
--   **Formalization Note** Measurability is needed for the expected reward of a randomized policy to be defined; histories range over a countable set, so no condition in the history is needed.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, p.9; §2.3, p.15

import Mathlib
import Definitions.Def_GreedyReusableNet_Rule

open MeasureTheory

namespace GreedyReusableNet

/-- **The admissible online policies** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1, p.9, and
§2.3, p.15): the initial seed is drawn from a probability measure and, for each period and
history, the proposed action set is a measurable function of the initial seed and the period
seed. This is the class the benchmark OPT ranges over.

**Formalization Note** Measurability is what makes a randomized policy's expected reward
meaningful (a Bochner integral of a non-measurable integrand would be `0`); histories range over
a countable set, so no further condition is needed. -/
def IsAdmissible {N : ℕ} (ρ : Rule N) : Prop :=
  IsProbabilityMeasure ρ.seedLaw ∧
    ∀ (t : ℕ) (h : History N) (A : Finset (Finset (Fin N))),
      MeasurableSet {p : ℝ × ℝ | ρ.act p.1 t h p.2 = A}

end GreedyReusableNet


