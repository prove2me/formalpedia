-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtMismatch
-- name    : ParetoNCSched_Supplement_rtMismatch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:35:11.265492+00:00
-- url     : https://prove2.me/theorems/714be05b-8ae9-4540-86fd-b3cc98bb543c
-- title:
--   A mismatch has occurred in the run of $\mathrm{RT}_L$
-- statement:
--   In the run of $\mathrm{RT}_L$ with predicted sizes $y$, a job $j$ **mismatches** if it completes with elapsed time different from $y_j$, or reaches elapsed time $y_j$ without completing. A mismatch has occurred at a state with elapsed times $e$ if some job has completed with $p_j\ne y_j$, or has $e_j\ge y_j$ without having completed.
--
--   **Formalization Note** Elapsed times only increase and completed jobs keep $e_j=p_j$, so once a mismatch has occurred the predicate stays true; detection is active from time $0$, including the first stage. The state of the run is the base mission's record (time, elapsed times, cost so far).
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 4.5, p.13; Appendix H, p.40

import Mathlib
import Definitions.Def_ParetoNCSched_MState

namespace ParetoNCSched.Supplement

/-- **A mismatch has occurred.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 4.5, p.13, and Appendix H, p.40: "a job j mismatches
if it completes with elapsed time different from yj, or reaches elapsed time yj without
completing."

At a state of the run (elapsed times `e`), some job has completed (`e_i ≥ p_i`) with
`p_i ≠ y_i`, or has elapsed time at least `y_i` without having completed.

**Formalization Note.** The run's state `(time, e, F)` is the base mission's `MState`. Elapsed
times only increase and a completed job keeps `e_i = p_i`, so once true this stays true: the
first mismatch is the first state at which it holds. Detection is active from time `0`. -/
def rtMismatch {n : ℕ} (p y : Fin n → ℝ) (s : MState n) : Prop :=
  ∃ i, (p i ≤ s.e i ∧ p i ≠ y i) ∨ (y i ≤ s.e i ∧ s.e i < p i)

end ParetoNCSched.Supplement


