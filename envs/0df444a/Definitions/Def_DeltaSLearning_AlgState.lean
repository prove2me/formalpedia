-- Prove2me | Definitions.Def_DeltaSLearning_AlgState
-- name    : DeltaSLearning_AlgState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:44.534989+00:00
-- url     : https://prove2.me/theorems/45c01b5e-c96a-4f14-a1fb-98d35f381fbb
-- title:
--   State of the $(\delta,S)$ learning algorithm at an epoch start
-- statement:
--   The state of the $(\delta,S)$ learning algorithm at the beginning of epoch $n$: the first period of the epoch, the beginning inventory $x^n$, the targets $S^n_j$, the cumulative simulated cycle pseudo costs $\hat G^{n-1}_j$ and lengths $\hat L^{n-1}_j$, the active set $\mathcal A^n\subseteq[J]$, and, for bookkeeping, the total pseudo cost incurred in all earlier periods.
--
--   **Formalization Note** Indices $j$ are natural numbers as in the paper; values at indices outside the active set are never read. The cost field is not part of the algorithm; it records what the regret charges.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), §3.3 steps (0b)–(0d), p.13; Algorithm 1, p.15

import Mathlib

namespace DeltaSLearning

/-- The state of the `(δ, S)` learning algorithm at the beginning of an epoch `n`: its first
period `t` (0-based), the beginning inventory `x = xⁿ`, the targets `S j = Sⁿ_j`, the
cumulative cycle pseudo costs `Ghat j = Ĝⁿ⁻¹_j` and lengths `Lhat j = L̂ⁿ⁻¹_j`, the active
set `A = 𝒜ⁿ ⊆ {1, …, J}`, and the total pseudo cost `cost` incurred in all earlier periods.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), §3.3 steps (0b)–(0d), p.13, and Algorithm 1, p.15.

**Formalization Note** Indices `j` are natural numbers, as in the paper (`[J] = {1, …, J}`);
values at indices outside the active set are never read. The field `cost` is bookkeeping for the
regret, not part of the algorithm. -/
structure AlgState where
  t : ℕ
  x : ℝ
  S : ℕ → ℝ
  Ghat : ℕ → ℝ
  Lhat : ℕ → ℝ
  A : Finset ℕ
  cost : ℝ

end DeltaSLearning


