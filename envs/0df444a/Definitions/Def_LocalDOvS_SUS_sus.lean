-- Prove2me | Definitions.Def_LocalDOvS_SUS_sus
-- name    : LocalDOvS_SUS_sus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:28:30.364958+00:00
-- url     : https://prove2.me/theorems/8ac7bdd2-992e-4fcd-8f41-4e8f5c128770
-- title:
--   Corrected shrinking uniform sampling algorithm
-- statement:
--   The **corrected shrinking uniform sampling (SUS) algorithm** with inputs $N,\sigma,\epsilon,\delta$, a rule choosing the Type-I pair and a rule breaking a final tie, as a sequential algorithm: after a history $h$, its next step is the one given by replaying the algorithm on $h$ from the initial state.
--
--   **Formalization Note** It differs from the printed Algorithm 2 in two places: the Type-I test is made once per active-set size, when condition (ii) holds (line 10), and $T_{\max}=N^2$ (line 2).
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, pp.15–16 (corrected)

import Mathlib
import Definitions.Def_LocalDOvS_SUS_susGo
import Definitions.Def_LocalDOvS_SUS_initState
import Definitions.Def_LocalDOvS_SUS_SeqAlg

open scoped NNReal

namespace LocalDOvS.SUS

/-- The corrected shrinking uniform sampling (SUS) algorithm as a sequential algorithm
(Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2, pp.15–16), with inputs `N, σ, ε, δ`, a
rule `pick` choosing the Type-I pair and a rule `tie` breaking a tie in the final comparison.
After a history `h`, its next step is that of `susGo` started from `initState N` with fuel `N`.

**Formalization Note (correction).** Two edits of the printed algorithm: the Type-I test
(line 10) is made once per active-set size, when condition (ii) holds, and `T_max = N²`
(line 2). See `lookStep` and `alphaSUS`. -/
noncomputable def sus (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ)
    (pick : SUSState → (ℕ → ℕ → ℝ) → ℕ × ℕ) (tie : SUSState → (ℕ → ℕ → ℝ) → Bool) :
    SeqAlg :=
  fun h => (susGo N σ ε δ pick tie h N (initState N)).2

end LocalDOvS.SUS


