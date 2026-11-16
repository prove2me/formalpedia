-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtGroup
-- name    : ParetoNCSched_Supplement_rtGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:36:10.940537+00:00
-- url     : https://prove2.me/theorems/690cd8f2-4d9f-49bf-8ad8-34866567ea7b
-- title:
--   The unfinished jobs of smallest elapsed time
-- statement:
--   At a state of the run, the set of unfinished jobs whose elapsed time is minimal among the unfinished jobs. In the first stage of $\mathrm{RT}_L$ all unfinished jobs share one elapsed time, so this is the set of all unfinished jobs.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, line 4, p.13

import Mathlib
import Definitions.Def_ParetoNCSched_unfinished

namespace ParetoNCSched.Supplement

open Classical in
/-- **The unfinished jobs of smallest elapsed time.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, line 4, p.13 ("Round-Robin
on the unfinished jobs of smallest elapsed time"), and Section 1.1, p.4.

**Formalization Note.** In the first stage of `RT_L` all unfinished jobs share one elapsed time,
so this is the set of all unfinished jobs, and Round-Robin on it is the first stage's
Round-Robin. -/
noncomputable def rtGroup {n : ℕ} (p : Fin n → ℝ) (s : MState n) : Finset (Fin n) :=
  (unfinished p s).filter fun i => ∀ k ∈ unfinished p s, s.e i ≤ s.e k

end ParetoNCSched.Supplement


