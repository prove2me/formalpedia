-- Prove2me | Definitions.Def_OnlineConvexOpt_Introduction_RandomizedWeightedMajority
-- name    : OnlineConvexOpt_Introduction_RandomizedWeightedMajority
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:05:14.723214+00:00
-- url     : https://prove2.me/theorems/27684c74-d876-4cd7-8574-735a447e3939
-- title:
--   One run of the Randomized Weighted Majority algorithm
-- statement:
--   Defines `IsRandomizedWeightedMajorityRun`, one run of the Randomized Weighted Majority
--   algorithm (RWM, Hazan §1.3.2, p. 11) with $N$ experts and decay parameter
--   $\varepsilon \in (0, 1/2)$. The weights `W` follow the same update as Weighted Majority
--   ($W_0(i) = 1$; an expert who erred at round $t$ has its weight scaled by $(1-\varepsilon)$,
--   a correct expert's weight is unchanged), but instead of following the majority, RWM samples an
--   expert with probability proportional to its weight and follows that expert's prediction:
--
--   $$
--   p_t(i) = \frac{W_t(i)}{\sum_j W_t(j)}.
--   $$
--
--   **Formalization Note.** As with Weighted Majority, this is a `Prop`-valued run predicate on
--   `expertPredict`, `outcome`, `W` and the probability vector `p`, not an executable sampler.
--   Randomization itself is not modelled measure-theoretically here — `p` is exactly the vector the
--   book calls the algorithm's mixed strategy, and Lemma 1.4's `expectedMistakes` (defined alongside
--   this structure) takes its expectation as the deterministic inner product $\sum_i p_t(i)\cdot
--   \mathbb 1[\text{expert } i \text{ erred at } t]$, matching the book's own identification in
--   §1.3.3.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 11, §1.3.2

import Mathlib

namespace OnlineConvexOpt.Introduction

variable {N : ℕ}

/-- One run of the Randomized Weighted Majority algorithm (RWM, §1.3.2, p. 11) with `N`
experts and decay parameter `ε`, against adversarially chosen expert predictions
`expertPredict` and true outcomes `outcome`. `W` are the same weights as Weighted Majority
(`W 0 i = 1`, correct experts keep their weight, mistaken experts are scaled by `(1 - ε)`);
`p` is the probability RWM assigns to each expert at each round,
`p_t(i) = W_t(i) / ∑_j W_t(j)`. -/
structure IsRandomizedWeightedMajorityRun (ε : ℝ) (expertPredict : ℕ → Fin N → Bool)
    (outcome : ℕ → Bool) (W : ℕ → Fin N → ℝ) (p : ℕ → Fin N → ℝ) : Prop where
  weight_init : ∀ i, W 0 i = 1
  weight_update : ∀ t i, W (t + 1) i =
    if expertPredict t i = outcome t then W t i else W t i * (1 - ε)
  prob_def : ∀ t i, p t i = W t i / ∑ j, W t j

/-- Expected number of mistakes RWM makes over rounds `0, …, T - 1`, `E[M_T]` in the book's
notation: at each round the algorithm errs with probability equal to the total probability
mass on mistaken experts, `∑_i p_t(i) · 1[\text{expert } i \text{ erred at } t]`. -/
noncomputable def expectedMistakes {N : ℕ} (expertPredict : ℕ → Fin N → Bool)
    (outcome : ℕ → Bool) (p : ℕ → Fin N → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ i, p t i * (if expertPredict t i ≠ outcome t then (1 : ℝ) else 0)

end OnlineConvexOpt.Introduction


