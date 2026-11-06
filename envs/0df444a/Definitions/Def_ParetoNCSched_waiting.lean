-- Prove2me | Definitions.Def_ParetoNCSched_waiting
-- name    : ParetoNCSched_waiting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:38.231557+00:00
-- url     : https://prove2.me/theorems/f54c62fd-026c-4cc8-a5a8-3f5c78b5d354
-- title:
--   The waiting jobs: unfinished jobs other than $j$
-- statement:
--   The *waiting jobs* are the $N-1$ unfinished jobs other than the committed job $j$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 3, p.8; Appendix B, Notation, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_unfinished

namespace ParetoNCSched

/-- **The waiting jobs.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 3, p.8, and Appendix B, Notation, p.17: "the waiting jobs
are the N − 1 unfinished jobs other than j". -/
noncomputable def waiting {n : ℕ} (p : Fin n → ℝ) (s : MState n) (j : Fin n) : Finset (Fin n) :=
  (unfinished p s).erase j

end ParetoNCSched


