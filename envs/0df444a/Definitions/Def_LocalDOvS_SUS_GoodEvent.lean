-- Prove2me | Definitions.Def_LocalDOvS_SUS_GoodEvent
-- name    : LocalDOvS_SUS_GoodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:27:16.939334+00:00
-- url     : https://prove2.me/theorems/237ce1fc-d224-4e0c-b07e-1202e4db4b53
-- title:
--   Good event: all confidence intervals correct
-- statement:
--   The **good event** for an objective $f$ is the set of tapes on which every confidence interval the algorithm can use is correct:
--
--   $$
--   G=\Big\{\omega:\ |\hat F_n(x)-f(x)|\le h(n,\sigma,\alpha)\ \text{ for all }x\in[N],\ n\in L\Big\},
--   $$
--
--   with $\hat F_n(x)$ the mean of the first $n$ tape entries of $x$. It is the event on which the correctness argument of the proof of Theorem 2 runs.
--
--   **Formalization Note** The event is about the tape, not the run; since the algorithm only uses means of the first $n\in L$ outputs of a point, adaptivity does not enter.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, proof of Theorem 2, pp.ec15–ec16 (corrected union bound)

import Mathlib
import Definitions.Def_LocalDOvS_SUS_sampleSizes
import Definitions.Def_LocalDOvS_SUS_sampleMean
import Definitions.Def_LocalDOvS_SUS_halfWidth

open scoped NNReal

namespace LocalDOvS.SUS

/-- The good event of the proof of Theorem 2 (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, pp.ec15–
ec16, "By the definition of confidence intervals", corrected union bound): the set of tapes on
which every confidence interval the algorithm can use is correct,
`|F̂_n(x) − f(x)| ≤ h(n, σ, α)` for all `x ∈ [N]` and all `n ∈ L = sampleSizes`, with `F̂_n(x)`
the mean of the first `n` tape entries of `x`.

**Formalization Note.** The event is about the tape, not the run: since the algorithm only ever
uses means of the first `n ∈ L` outputs of a point, no adaptivity enters. -/
def GoodEvent (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ) (f : ℕ → ℝ) : Set (ℕ × ℕ → ℝ) :=
  {ω | ∀ x ∈ Finset.Icc 1 N, ∀ n ∈ sampleSizes N σ ε δ,
    |sampleMean (fun x j => ω (x, j)) x n - f x| ≤ halfWidth σ (alphaSUS N δ) n}

end LocalDOvS.SUS


