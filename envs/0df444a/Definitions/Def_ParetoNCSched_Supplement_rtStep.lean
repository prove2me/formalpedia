-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_rtStep
-- name    : ParetoNCSched_Supplement_rtStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:39:03.819349+00:00
-- url     : https://prove2.me/theorems/dc9151bc-088c-4d94-929f-c2dec155e08b
-- title:
--   One step of the run of $\mathrm{RT}_L$
-- statement:
--   From a state $(t,e,F)$ of the run, let $\Delta$ be the least candidate length. The rates of the state are used for time $\Delta$: the time becomes $t+\Delta$, each elapsed time $e_i+\Delta r_i$, and the cost so far $F+N\Delta$, where $N$ is the number of unfinished jobs.
--
--   **Formalization Note** With no unfinished job there is no candidate, $\Delta=0$ and the state is final.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_rtCands

namespace ParetoNCSched.Supplement

/-- **One step of the run of `RT_L`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13. From the state `(t, e, F)`, with
`Δ` the least candidate length (`rtCands`), the rates of `rtRates` are used for time `Δ`: the
time increases by `Δ`, each `e_i` by `Δ r_i`, and the cost so far `F` by `N Δ` (`N` the number of
unfinished jobs).

**Formalization Note.** With no unfinished job there is no candidate, `Δ = sInf ∅ = 0` and the
state is final. Otherwise the candidate set is finite and non-empty (the served jobs' completion
durations are positive), so `Δ` is its minimum. -/
noncomputable def rtStep {n : ℕ} (L : ℝ) (p y : Fin n → ℝ) (s : MState n) : MState n :=
  ⟨s.time + sInf (rtCands L p y s), s.e + sInf (rtCands L p y s) • rtRates L p y s,
    s.F + ((unfinished p s).card : ℝ) * sInf (rtCands L p y s)⟩

end ParetoNCSched.Supplement


