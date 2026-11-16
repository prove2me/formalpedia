-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_algStep
-- name    : ParetoNCSched_Supplement_algStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:28:27.357858+00:00
-- url     : https://prove2.me/theorems/9613ca7e-41b6-4828-9340-e88a90d60dc8
-- title:
--   One completion step of the run of a deterministic algorithm
-- statement:
--   If some job not in the history ever reaches its size under the rate function followed from the state, let $C_{k+1}$ be the first such time. Every job not in the history with $e_j(C_{k+1})\ge p_j$ is appended to the history with completion time $C_{k+1}$, in increasing order of index, and the rate function followed so far becomes the run's rate function before $C_{k+1}$. If no remaining job ever completes, the state does not change: the run follows the current rate function forever and the remaining jobs never complete.
--
--   **Formalization Note** For a valid algorithm the elapsed times are continuous, so the infimum is attained and at least one job is appended at each effective step.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_nextCands

namespace ParetoNCSched.Supplement

open Classical in
/-- **One completion step of the run of a deterministic algorithm.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model,
p.15: "after the k-th completion, the algorithm follows the rate function of the current history
until the next completion", histories listing "simultaneous completions … by index".

If some job not in the history ever reaches its size under the rate function followed from the
state, let `C_{k+1}` be the first such time (the infimum of `nextCands`); every job not in the
history whose elapsed time is at least its size at `C_{k+1}` is appended to the history with
completion time `C_{k+1}`, in increasing index order, and the rate function followed so far is
stored as the run's rate function before `C_{k+1}`. If no remaining job ever completes, the state
is unchanged (the run follows the current rate function forever).

**Formalization Note.** Under a valid algorithm the elapsed times are continuous, so the
infimum is attained and at least one job is appended. -/
noncomputable def algStep {M : PredModel} (A : DetAlg M) {n : ℕ} (p : Fin n → ℝ)
    (y : M.Pred n) (s : AlgRunState n) : AlgRunState n :=
  if (nextCands A p y s).Nonempty then
    { hist := s.hist ++
        ((Finset.univ.filter fun j => j ∉ s.hist.map Prod.fst ∧
            p j ≤ elapsed (curRate A y s) j (sInf (nextCands A p y s))).sort).map
          (fun j => (j, sInf (nextCands A p y s)))
      last := sInf (nextCands A p y s)
      rate := curRate A y s }
  else s

end ParetoNCSched.Supplement


