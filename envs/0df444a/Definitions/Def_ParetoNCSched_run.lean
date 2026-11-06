-- Prove2me | Definitions.Def_ParetoNCSched_run
-- name    : ParetoNCSched_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:16:46.303972+00:00
-- url     : https://prove2.me/theorems/1f99b704-06f1-4eba-a5e5-d580728635d2
-- title:
--   The run of $\mathrm{MRC}_R$: state after $k$ steps
-- statement:
--   The run of $\mathrm{MRC}_R$ on sizes $p$ with predicted order $\sigma$ starts at $t_0=0$ with all elapsed times and the cost equal to $0$ and proceeds interval by interval; its $k$-th state is the $k$-fold iterate of one step.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_step

namespace ParetoNCSched

/-- **The run of `MRC_R`: the state after `k` steps.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, p.17: "Let t₀ = 0", all
elapsed times and the cost are `0` at time `0`, and the run proceeds interval by interval.

**Formalization Note.** `run R p σ k` is the `k`-th iterate of `step` from `(0, 0, 0)`. Once no job is
unfinished the iteration is constant. -/
noncomputable def run {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) : MState n :=
  (step R p σ)^[k] ⟨0, 0, 0⟩

end ParetoNCSched


