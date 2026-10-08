-- Prove2me | Definitions.Def_NagaevLD_LowerBound_Setting
-- name    : NagaevLD_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:53.928262+00:00
-- url     : https://prove2.me/theorems/d4b60bcd-c2ff-42b5-a2da-782b31ea5a3c
-- title:
--   §0–§1, pp. 745, 758 — the sums S_n and S_n^j, B_n² = ΣVar X_i, and P_j = P(S_n ≥ x, X_j ≥ x, max_{i≠j}X_i < x)
-- statement:
--   Let $X_1,\dots,X_n$ be real random variables on a probability space $(\Omega,\mathcal F,P)$. This file fixes the following objects of S. V. Nagaev's survey of large deviations (§0, p. 745, and the end of §1, p. 758).
--
--   1. The **sum** and the **sum without the $j$-th term**:
--   $$S_n=\sum_{i=1}^n X_i,\qquad S_n^j=\sum_{i\ne j}X_i=S_n-X_j .$$
--   2. The **sum of variances** $$B_n^2=\sum_{i=1}^n\sigma_i^2,\qquad \sigma_i^2=\operatorname{Var}X_i ,$$ and $B_n=(B_n^2)^{1/2}$.
--   3. For a level $x$ and an index $j$, the probability that the sum exceeds $x$ *because of the single summand $X_j$*:
--   $$P_j=P\Big(S_n\ge x,\ X_j\ge x,\ \max_{i\ne j}X_i<x\Big).$$
--
--   These are the quantities in which the paper's lower bound $P(S_n\ge x)\ge\tfrac12\sum_j P(X_j\ge 2x)$ is proved: $P_j$ isolates the event that exactly one summand is large.
--
--   **Formalization Note** The summands are indexed by `Fin n`, so the paper's $X_1,\dots,X_n$ are `X 0, …, X (n-1)`. The condition $\max_{i\ne j}X_i<x$ is written "$X_i<x$ for every $i\ne j$"; for $n=1$ there is no such $i$ and the condition is the whole space, which is what the argument requires there. Mathlib's `variance` returns $0$ for a variable that is not square integrable, so every statement that uses $B_n^2$ also assumes each $X_i\in L^2(P)$, which is the paper's hypothesis $B_n^2<\infty$.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 745, §0 (σ_i², B_n², S_n); p. 758, (1.57) (P_j) and S_n^j

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.LowerBound

open MeasureTheory ProbabilityTheory

/-- `Sj n X j` is `S_n^j = Σ_{i ≠ j} X_i = S_n − X_j` (Nagaev 1979, §1, p. 758). -/
def Sj {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (j : Fin n) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, X i ω

/-- `Pj P X x j` is `P_j = P(S_n ≥ x, X_j ≥ x, max_{i≠j} X_i < x)` of (1.57) (Nagaev 1979, p. 758).
The condition `max_{i≠j} X_i < x` is written `∀ i, i ≠ j → X i ω < x`, which for `n = 1` (no `i ≠ j`)
is the whole space. -/
noncomputable def Pj {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (x : ℝ) (j : Fin n) : ℝ :=
  P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω ∧ x ≤ X j ω ∧ ∀ i, i ≠ j → X i ω < x}

end NagaevLD.LowerBound


