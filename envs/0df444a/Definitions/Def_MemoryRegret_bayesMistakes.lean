-- Prove2me | Definitions.Def_MemoryRegret_bayesMistakes
-- name    : MemoryRegret_bayesMistakes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:18.019192+00:00
-- url     : https://prove2.me/theorems/87c7427e-0265-4aaa-b4db-c35d93c20079
-- title:
--   Expected mistakes $\mathbb E[M^*]$ of the Bayes-optimal online predictor
-- statement:
--   For a law $P$ of $(Y_1,\dots,Y_T)\in\{0,1\}^T$, the **Bayes-optimal online predictor** knows $P$ and predicts at each round the most likely label given the labels seen so far. Its expected number of mistakes is
--   $$\mathbb E[M^*]=\sum_{t}\ \sum_{z\in\{0,1\}^{t-1}}\min\bigl(P[Y_{<t}=z,Y_t=0],\ P[Y_{<t}=z,Y_t=1]\bigr).$$
--
--   **Formalization Note** The predictor errs at round $t$ after the prefix $z$ with exactly the smaller of the two probabilities, so this sum needs no conditional probabilities and ties do not matter.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), §6.1, p.34

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec

namespace MemoryRegret

/-- **The expected number of mistakes `E[M*]` of the Bayes-optimal online predictor.**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
§6.1, p.34: "the Bayes-optimal predictor … knowing the data-generating distribution, predicts at
each round the most likely label conditioned on all previously observed labels."

For a law `P` of `(Y_0, …, Y_{T−1}) ∈ {0,1}^T`,
`bayesMistakes P = ∑_t ∑_{z ∈ {0,1}^t} min(P[Y_{<t} = z, Y_t = 0], P[Y_{<t} = z, Y_t = 1])`.

**Formalization Note.** The Bayes-optimal predictor errs at round `t` after the prefix `z` with
probability `min` of the two conditional probabilities, so its expected mistakes are this sum
(ties do not matter); no conditional probabilities are needed. Rounds are 0-based. -/
noncomputable def bayesMistakes {T : ℕ} (P : (Fin T → Bool) → ℝ) : ℝ :=
  ∑ t : Fin T, ∑ z : Fin t → Bool,
    min (wprob P fun y => (fun j => y (Fin.castLE t.2.le j)) = z ∧ y t = false)
        (wprob P fun y => (fun j => y (Fin.castLE t.2.le j)) = z ∧ y t = true)

end MemoryRegret


