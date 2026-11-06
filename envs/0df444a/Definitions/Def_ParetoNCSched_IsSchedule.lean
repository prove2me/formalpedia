-- Prove2me | Definitions.Def_ParetoNCSched_IsSchedule
-- name    : ParetoNCSched_IsSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:24.557116+00:00
-- url     : https://prove2.me/theorems/b3502c3a-8768-4224-b048-c811b212a479
-- title:
--   Preemptive single-machine schedule (measurable rates summing to at most $1$)
-- statement:
--   A *schedule* for $n$ jobs on one machine assigns to every job $j$ a measurable rate function $t\mapsto r_j(t)\ge 0$ with
--   $$\sum_j r_j(t)\le 1\qquad\text{for every }t.$$
--   Jobs may be preempted and the machine may be shared among several jobs.
--
--   **Formalization Note** A rate function is a map $r:\mathbb R\to\mathbb R^n$; the conditions are imposed at every real time. Only times $t\ge0$ influence elapsed and completion times, and every schedule on $[0,\infty)$ extends by $0$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Notation, p.15; Section 2, Model, p.7

import Mathlib

namespace ParetoNCSched

/-- **Preemptive single-machine schedule.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Notation, p.15: "A schedule assigns to
every job a measurable rate rⱼ(t) ≥ 0, with Σⱼ rⱼ(t) ≤ 1" (and Section 2, p.7: "At every time
t ≥ 0, the algorithm chooses rates rⱼ(t) ≥ 0 with Σⱼ rⱼ(t) ≤ 1").

**Formalization Note.** A rate function is `r : ℝ → Fin n → ℝ` (time, job); the conditions are
required at every real time. Only `[0, ∞)` matters for elapsed and completion times, and every
schedule on `[0, ∞)` extends by `0`, so the set of costs is the paper's. -/
def IsSchedule {n : ℕ} (r : ℝ → Fin n → ℝ) : Prop :=
  (∀ j, Measurable fun t => r t j) ∧ (∀ t j, 0 ≤ r t j) ∧ ∀ t, ∑ j, r t j ≤ 1

end ParetoNCSched


