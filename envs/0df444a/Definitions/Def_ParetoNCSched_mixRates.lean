-- Prove2me | Definitions.Def_ParetoNCSched_mixRates
-- name    : ParetoNCSched_mixRates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:33.486588+00:00
-- url     : https://prove2.me/theorems/b441c622-4f5a-49bc-9066-736a50281162
-- title:
--   Rate vector: $j$ at rate $a$, each waiting job at $(1-a)/(N-1)$
-- statement:
--   For a number $a$, the rate vector that runs the committed job $j$ at rate $a$, each waiting job at rate $(1-a)/(N-1)$, and completed jobs at rate $0$.
--
--   **Formalization Note** $a$ is a free parameter (Lemma B.2 considers every $a\in[1/N,1]$); the algorithm uses $a$ of its branch.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 10, p.9; Lemma B.2, p.18

import Mathlib
import Definitions.Def_ParetoNCSched_waiting

namespace ParetoNCSched

/-- **Rate vector "j at rate a, each waiting job at rate (1 − a)/(N − 1)".** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1,
line 10, p.9, and Lemma B.2, p.18. Completed jobs get rate `0`.

**Formalization Note.** The parameter `a` is arbitrary (Lemma B.2 considers every `a ∈ [1/N, 1]`);
the algorithm uses `a = commitRate`. -/
noncomputable def mixRates {n : ℕ} (p : Fin n → ℝ) (s : MState n) (j : Fin n) (a : ℝ) : Fin n → ℝ :=
  fun i => if i = j then a
    else if i ∈ waiting p s j then (1 - a) / (((unfinished p s).card : ℝ) - 1) else 0

end ParetoNCSched


