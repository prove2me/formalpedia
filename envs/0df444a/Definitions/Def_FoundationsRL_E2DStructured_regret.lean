-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_regret
-- name    : FoundationsRL_E2DStructured_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:22:07.657234+00:00
-- url     : https://prove2.me/theorems/136d87cb-0e57-4a25-b3ed-21b2b844c737
-- title:
--   The regret of a sequence of decision distributions
-- statement:
--   For a true reward function $f^\star$ and distributions $p^1,\dots,p^T$, the regret is
--   $$\mathrm{Reg}=\sum_{t=1}^T\mathbb E_{\pi^t\sim p^t}\big[f^\star(\pi^\star)-f^\star(\pi^t)\big],$$
--   where $\pi^\star$ maximizes $f^\star$. It is measured in expectation over the learner's internal randomization, so given the distributions it involves no further randomness.
--
--   **Formalization Note** Rounds are indexed $0,\dots,T-1$. The value lies in $[0,\infty]$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.1, (4.3), p. 57; p. 66

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_expectedGap

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The regret `Reg = ∑_{t=1}^T E_{π^t∼p^t}[f⋆(π⋆) − f⋆(π^t)]` of a sequence of decision
distributions (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.1, p. 57, (4.3); p. 66, first display of the proof of Proposition 13).

**Formalization Note.** Rounds are indexed `0, …, T − 1`. The value lies in `[0, ∞]`, see
`expectedGap`. -/
noncomputable def regret {D : Type*} [MeasurableSpace D] (T : ℕ) (fstar : D → ℝ)
    (p : ℕ → ProbabilityMeasure D) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range T, expectedGap fstar (p t)

end FoundationsRL.E2DStructured


