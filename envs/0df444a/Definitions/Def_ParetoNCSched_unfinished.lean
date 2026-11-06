-- Prove2me | Definitions.Def_ParetoNCSched_unfinished
-- name    : ParetoNCSched_unfinished
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:21.928381+00:00
-- url     : https://prove2.me/theorems/3192d6de-f2f8-46e5-b6f2-06746f979480
-- title:
--   Unfinished jobs of a state: $e_i<p_i$
-- statement:
--   In a state with elapsed times $e$, job $i$ is completed if and only if $e_i=p_i$ (it receives no processing afterwards), and unfinished if $e_i<p_i$. $N$ denotes the number of unfinished jobs.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, Notation, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_MState

namespace ParetoNCSched

/-- **Unfinished jobs of a state.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, Notation, p.17: "A job i is completed if and
only if eᵢ = pᵢ; it receives no processing afterwards." A job is unfinished when `eᵢ < pᵢ`; `N` is
the number of unfinished jobs. -/
noncomputable def unfinished {n : ℕ} (p : Fin n → ℝ) (s : MState n) : Finset (Fin n) :=
  Finset.univ.filter fun i => s.e i < p i

end ParetoNCSched


