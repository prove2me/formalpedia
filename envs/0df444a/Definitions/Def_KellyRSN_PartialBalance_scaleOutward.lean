-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_scaleOutward
-- name    : KellyRSN_PartialBalance_scaleOutward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:38:02.90055+00:00
-- url     : https://prove2.me/theorems/8fbf8d52-6ca6-40b3-8f97-16798ac7664b
-- title:
--   Rates out of $\mathcal A$ multiplied by $c$
-- statement:
--   Given rates $q$ on $\mathcal S$, a set $\mathcal A$ and $c \ge 0$, the **altered rates** are
--   $$
--   q^c(j,k) = \begin{cases} c\, q(j,k), & j \in \mathcal A \text{ and } k \in \mathcal S - \mathcal A,\\ q(j,k), & \text{otherwise.} \end{cases}
--   $$
--
--   Only the transitions **from** $\mathcal A$ **to** its complement are scaled; transitions from $\mathcal S - \mathcal A$ into $\mathcal A$ keep their rates. This is the alteration in Exercise 1.6.4 and Theorem 9.5 (iv).
--
--   **Formalization Note** $c$ is a non-negative real number.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 27 (PDF p. 30), Exercise 1.6.4; p. 200 (PDF p. 203), Theorem 9.5 (iv)

import Mathlib

open scoped ENNReal NNReal

namespace KellyRSN.PartialBalance

open Classical in
/-- **Rates out of `𝒜` multiplied by `c`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.6.4, p. 27 (PDF p. 30) and
Theorem 9.5 (iv), p. 200 (PDF p. 203): "the process is altered by changing the transition rate
`q(j, k)` to `c q(j, k)` for `j ∈ 𝒜`, `k ∈ 𝒮 − 𝒜`".

`scaleOutward q A c j k = c * q j k` if `j ∈ A` and `k ∉ A`, and `q j k` otherwise. Only the rates
**from** `A` **to** its complement are scaled; rates from the complement into `A` are unchanged.

**Formalization Note.** `c : ℝ≥0` (a non-negative real multiplier, coerced to `ℝ≥0∞`). -/
noncomputable def scaleOutward {S : Type*} (q : S → S → ℝ≥0∞) (A : Set S) (c : ℝ≥0) :
    S → S → ℝ≥0∞ :=
  fun j k => if j ∈ A ∧ k ∉ A then (c : ℝ≥0∞) * q j k else q j k

end KellyRSN.PartialBalance


