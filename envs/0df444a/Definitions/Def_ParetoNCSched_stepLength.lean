-- Prove2me | Definitions.Def_ParetoNCSched_stepLength
-- name    : ParetoNCSched_stepLength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:13:42.425494+00:00
-- url     : https://prove2.me/theorems/ce781336-dceb-46e8-a1f1-3d3c6308f0a3
-- title:
--   Length $t_{k+1}-t_k$ of a step of $\mathrm{MRC}_R$
-- statement:
--   The length of the step from $t_k$ is the smallest event candidate, $t_{k+1}-t_k=\min\{u>0: \text{an event occurs after }u\}$.
--
--   **Formalization Note** Written as the infimum of the candidate set. If that set were empty the value would be $0$ and the run would stop advancing, leaving some job unfinished forever, so that its completion time is $+\infty$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_eventCands

namespace ParetoNCSched

/-- **Length `t_{k+1} − t_k` of a step of the run.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, p.17: `t_{k+1}` is "the first
time t > t_k at which one of the following events occurs".

**Formalization Note.** The infimum of the (finite) set of event candidates. If the set were empty
the value would be `0` and the run would stop progressing, so that some completion time is `⊤`;
this makes a broken run falsify, not trivialize, the upper bounds. -/
noncomputable def stepLength {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (s : MState n) (j : Fin n) : ℝ :=
  sInf (eventCands R p s j)

end ParetoNCSched


