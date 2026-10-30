-- Prove2me | Definitions.Def_FoundationsRL_DECLower_avgActionDist
-- name    : FoundationsRL_DECLower_avgActionDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:11:45.47681+00:00
-- url     : https://prove2.me/theorems/9bcd2fd9-b177-4f9f-a351-2fdb2e612226
-- title:
--   Average action distribution $p_M=\mathbb E^M[\frac1T\sum_t p_t]$
-- statement:
--   For an algorithm $p$, a kernel $M$ and a horizon $T\ge 1$, the **average action distribution** is
--
--   $$
--   p_M:=\mathbb E^M\left[\frac1T\sum_{t=1}^T p_t(\cdot\mid H_{t-1})\right]\in\Delta(\Pi),
--   $$
--
--   the expectation, under the history law $\mathbb P^M$, of the average of the decision distributions over the $T$ rounds.
--
--   It reduces the expected regret to a single expectation over decisions, (6.37), and it is compared across two models in the proof of Proposition 28.
--
--   **Formalization Note** At $T=0$, where $1/T$ is undefined, the Lean definition gives the zero measure.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 28, p. 108 (p_M)

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_Algorithm_policyAt
import Definitions.Def_FoundationsRL_DECLower_histLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **Average action distribution** `p_M := E_M[(1/T) Σ_{t=1}^T p_t] ∈ Δ(Π)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 28, p. 108.

`avgActionDist alg M T` is the measure `A ↦ E_{H_T ∼ P^M}[(1/T) Σ_t p_t(A | H_{t−1})]`.

**Formalization Note.** Literally the paper's expectation of the average of the round-`t`
decision distributions under the history law of the first `T` rounds (`Measure.bind` with the
kernel `policyAt`). 0-based rounds. For `T ≥ 1` and Markov `M` it is a probability measure; for
`T = 0` (where the paper's `1/T` is undefined) it is the zero measure. -/
noncomputable def avgActionDist {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (alg : Algorithm D O) (M : Kernel D (ℝ × O)) (T : ℕ) : Measure D :=
  (T : ℝ≥0∞)⁻¹ • ∑ t : Fin T, (histLaw alg M T).bind (alg.policyAt T t)

end FoundationsRL.DECLower


