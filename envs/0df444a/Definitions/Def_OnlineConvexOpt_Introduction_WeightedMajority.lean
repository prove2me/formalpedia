-- Prove2me | Definitions.Def_OnlineConvexOpt_Introduction_WeightedMajority
-- name    : OnlineConvexOpt_Introduction_WeightedMajority
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:04:54.523308+00:00
-- url     : https://prove2.me/theorems/3770684a-dc8b-4b43-b11f-29f20af3736f
-- title:
--   One run of the Weighted Majority algorithm
-- statement:
--   Defines `IsWeightedMajorityRun`, one run of the Weighted Majority algorithm (Hazan
--   §1.3.1, p. 9) with $N$ experts and decay parameter $\varepsilon \in (0, 1/2)$, against
--   adversarially chosen expert predictions and true outcomes (the book's actions $A$/$B$
--   represented by `true`/`false`). Weights start at $W_0(i) = 1$ for every expert $i$; at each
--   round, an expert whose prediction disagreed with the outcome has its weight scaled by
--   $(1-\varepsilon)$, while a correct expert's weight is unchanged:
--
--   $$
--   W_{t+1}(i) = \begin{cases} W_t(i) & \text{expert } i \text{ was correct at round } t, \\
--   (1-\varepsilon)\, W_t(i) & \text{expert } i \text{ erred at round } t. \end{cases}
--   $$
--
--   The algorithm's own prediction at round $t$, `algPredict t`, is fixed by the majority-vote
--   rule: it predicts `true` exactly when the total weight currently backing `true` is at least
--   the total weight backing `false`.
--
--   **Formalization Note.** `IsWeightedMajorityRun` is a `Prop`-valued structure relating the four
--   functions `expertPredict`, `outcome`, `W` and `algPredict`, rather than an executable recursive
--   definition, so the milestone theorem can quantify over any run satisfying it — including one
--   produced by an explicit recursive construction, which the audited statement does not fix.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 9, §1.3.1

import Mathlib

namespace OnlineConvexOpt.Introduction

variable {N : ℕ}

/-- One run of the Weighted Majority algorithm (§1.3.1, p. 9) with `N` experts and decay
parameter `ε`, against adversarially chosen expert predictions `expertPredict` and true
outcomes `outcome` (the book's actions `A`/`B` represented by `true`/`false`). `W` are the
algorithm's weights: `W 0 i = 1` for every expert, and at each round the weight of an expert
who erred is scaled by `(1 - ε)` while a correct expert's weight is unchanged. `algPredict` is
fixed by the majority-vote rule: the algorithm predicts `true` exactly when the total weight
currently backing `true` is at least the total weight backing `false`
(`a_t = A` if `W_t(A) ≥ W_t(B)` else `B`). -/
structure IsWeightedMajorityRun (ε : ℝ) (expertPredict : ℕ → Fin N → Bool)
    (outcome : ℕ → Bool) (W : ℕ → Fin N → ℝ) (algPredict : ℕ → Bool) : Prop where
  weight_init : ∀ i, W 0 i = 1
  weight_update : ∀ t i, W (t + 1) i =
    if expertPredict t i = outcome t then W t i else W t i * (1 - ε)
  predict_rule : ∀ t, algPredict t = true ↔
    (∑ i ∈ Finset.univ.filter (fun i => expertPredict t i = true), W t i) ≥
    (∑ i ∈ Finset.univ.filter (fun i => expertPredict t i = false), W t i)

end OnlineConvexOpt.Introduction


