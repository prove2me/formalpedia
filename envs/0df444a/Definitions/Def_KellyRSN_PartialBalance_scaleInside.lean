-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_scaleInside
-- name    : KellyRSN_PartialBalance_scaleInside
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:44.982163+00:00
-- url     : https://prove2.me/theorems/47da4eb7-0f5a-4484-943f-4d48a26c7b35
-- title:
--   Rates multiplied by $c$ inside $\mathcal A$
-- statement:
--   Given rates $q$ on $\mathcal S$, a set $\mathcal A$ and $c \ge 0$, the **altered rates** are
--   $$
--   q_c(j,k) = \begin{cases} c\, q(j,k), & j \in \mathcal A \text{ and } k \in \mathcal A,\\ q(j,k), & \text{otherwise.} \end{cases}
--   $$
--
--   This is the alteration in Exercise 1.6.3 and Theorem 9.5 (iii): the transitions within $\mathcal A$ are sped up or slowed down by the factor $c$.
--
--   **Formalization Note** $c$ is a non-negative real number.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 27 (PDF p. 30), Exercise 1.6.3; p. 200 (PDF p. 203), Theorem 9.5 (iii)

import Mathlib

open scoped ENNReal NNReal

namespace KellyRSN.PartialBalance

open Classical in
/-- **Rates multiplied by `c` inside `𝒜`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.6.3, p. 27 (PDF p. 30) and
Theorem 9.5 (iii), p. 200 (PDF p. 203): "the process is altered by changing the transition rate
`q(j, k)` to `c q(j, k)` for `j, k ∈ 𝒜`".

`scaleInside q A c j k = c * q j k` if `j ∈ A` and `k ∈ A`, and `q j k` otherwise.

**Formalization Note.** `c : ℝ≥0` (a non-negative real multiplier, coerced to `ℝ≥0∞`): rates are
non-negative, so only `c ≥ 0` yields a rate matrix. -/
noncomputable def scaleInside {S : Type*} (q : S → S → ℝ≥0∞) (A : Set S) (c : ℝ≥0) :
    S → S → ℝ≥0∞ :=
  fun j k => if j ∈ A ∧ k ∈ A then (c : ℝ≥0∞) * q j k else q j k

end KellyRSN.PartialBalance


