-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtRates
-- name    : ParetoNCSched_Supplement_rtRates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:37:06.215594+00:00
-- url     : https://prove2.me/theorems/63179b89-480b-49c4-a02c-eeaf8f98db84
-- title:
--   The rates of $\mathrm{RT}_L$
-- statement:
--   At a state of the run of $\mathrm{RT}_L$: in the second stage the next job in the order of $y$ runs alone at rate $1$; otherwise (first stage, or after the first mismatch) the machine is shared equally among the unfinished jobs of smallest elapsed time, each at rate $1/|G|$ for the group $G$ of such jobs. With no unfinished job nothing runs.
--
--   **Formalization Note** Round-Robin on the jobs of smallest elapsed time is levelling: a job joins the served group when the group's elapsed time reaches its own, which is an event of the run.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13; Appendix H, p.40

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_rtSeqMode
import Definitions.Def_ParetoNCSched_Supplement_rtGroup
import Definitions.Def_ParetoNCSched_Supplement_rtNext

namespace ParetoNCSched.Supplement

open Classical in
/-- **The rates of `RT_L` at a state.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, lines 2–4, p.13, and Appendix H, p.40.

In the second stage (`rtSeqMode`) the next job in the order of `y` runs alone at rate `1`.
Otherwise (first stage, or after the first mismatch) the machine is shared equally among the
unfinished jobs of smallest elapsed time (`rtGroup`), each at rate `1/|G|`; with no unfinished job
nothing runs.

**Formalization Note.** Stage 3, "Round-Robin on the unfinished jobs of smallest elapsed time", is
given by levelling: the minimal-elapsed jobs are served equally, and a job joins the served group
when the group's elapsed time reaches its own (an event of `rtCands`). In stage 1 the group is
every unfinished job. -/
noncomputable def rtRates {n : ℕ} (L : ℝ) (p y : Fin n → ℝ) (s : MState n) : Fin n → ℝ :=
  fun i =>
    if rtSeqMode L p y s then (if i ∈ rtNext p y s then 1 else 0)
    else (if i ∈ rtGroup p s then 1 / ((rtGroup p s).card : ℝ) else 0)

end ParetoNCSched.Supplement


