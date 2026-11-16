-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtCands
-- name    : ParetoNCSched_Supplement_rtCands
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:37:59.129972+00:00
-- url     : https://prove2.me/theorems/8cb8bc5f-0b10-425b-ac41-70d4936a0ed2
-- title:
--   Candidate lengths of the next step of $\mathrm{RT}_L$
-- statement:
--   Under the constant rates of a state, the positive durations after which an event of the run of $\mathrm{RT}_L$ occurs. In the second stage, with job $j$ running alone: $j$ reaches $p_j$ or $y_j$. Otherwise, with the group $G$ served at rate $1/|G|$ and $i\in G$: the group reaches $p_i$, $y_i$ or the level $L$, after $(p_i-e_i)|G|$, $(y_i-e_i)|G|$, $(L-e_i)|G|$, or it reaches the elapsed time $e_k$ of another unfinished job $k$, after $(e_k-e_i)|G|$.
--
--   These are the completions, the moments a mismatch can be detected, the end of the first stage and the merges of the levelling Round-Robin.
--
--   **Formalization Note** Breakpoints at which nothing changes leave the rates unchanged, since the rates depend only on the state.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13; Appendix H, p.40

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_rtRates

namespace ParetoNCSched.Supplement

/-- **Candidate lengths of the next step of `RT_L`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13, and Appendix H,
p.40. Under the constant rates of `rtRates`, the positive durations after which an event occurs:
* second stage, running job `j` at rate `1`: `j` reaches `p_j` (`p_j − e_j`) or `y_j`
  (`y_j − e_j`);
* otherwise, group `G` at rate `1/|G|`, for a job `i ∈ G`: it reaches `p_i`, `y_i` or the level
  `L` (after `(p_i − e_i)|G|`, `(y_i − e_i)|G|`, `(L − e_i)|G|`), or the group reaches the
  elapsed time `e_k` of an unfinished job `k` (after `(e_k − e_i)|G|`).

**Formalization Note.** These are completions, the moments a mismatch can be detected (reaching
`y_i`, completing at `p_i`), the end of the first stage (level `L`) and the merges of the
levelling Round-Robin. Breakpoints at which nothing changes (for example reaching `L` after a
mismatch) leave the rates unchanged, since the rates depend only on the state. Only positive
durations count; the next step length is the least one. -/
noncomputable def rtCands {n : ℕ} (L : ℝ) (p y : Fin n → ℝ) (s : MState n) : Set ℝ :=
  {u | 0 < u ∧
    ((rtSeqMode L p y s ∧ ∃ j ∈ rtNext p y s, u = p j - s.e j ∨ u = y j - s.e j) ∨
     (¬ rtSeqMode L p y s ∧ ∃ i ∈ rtGroup p s,
        u = (p i - s.e i) * (rtGroup p s).card ∨
        u = (y i - s.e i) * (rtGroup p s).card ∨
        u = (L - s.e i) * (rtGroup p s).card ∨
        ∃ k ∈ unfinished p s, u = (s.e k - s.e i) * (rtGroup p s).card))}

end ParetoNCSched.Supplement


