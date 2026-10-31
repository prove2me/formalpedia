-- Prove2me | Definitions.Def_CompetitionComplexity_Program
-- name    : CompetitionComplexity_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:43.403795+00:00
-- url     : https://prove2.me/theorems/deb35ce6-a8a4-4cdf-89e5-c02941ac7a76
-- title:
--   The infinite-dimensional program (1)–(4): feasible sequences $\delta$ and the objective
-- statement:
--   Fix $\varepsilon\ge0$ and positive integers $n,m$. The program (1)–(4) is over real sequences $(\delta_j)_{j\in\mathbb N}$:
--   $$
--   \text{minimize}\quad (1+\varepsilon)\sum_{i=0}^{m-1}\delta_i-\sum_{i=0}^{\infty}\Bigl(1-\Bigl(\frac{\delta_{i+1}}{\delta_i}\Bigr)^n\Bigr)\delta_i \tag{1}
--   $$
--   subject to
--
--   1. (2) $\delta_{j+1}\le\delta_j$ for every $j\ge0$,
--   2. (3) $\delta_j^2\le\delta_{j-1}\delta_{j+1}$ for every $j\ge1$,
--   3. (4) $\delta_0=1$ and $\delta_j>0$ for every $j\ge1$.
--
--   A sequence satisfying (2)–(4) is **feasible**. The **value** of the program is the infimum of (1) over feasible sequences; in general it is not attained. Theorem 3 says that $(1+\varepsilon)A_m(F)\ge M_n(F)$ for all $F$ exactly when this value is non-negative.
--
--   **Formalization Note** The series in (1) is Lean's `tsum`, which is $0$ for a non-summable family. On every feasible $\delta$ its terms are non-negative and bounded by $n(\delta_i-\delta_{i+1})$, so the series is summable and `tsum` is its sum (proved in the mission's verification file). The value is never formed with `sInf`: statements quantify over feasible sequences or use a greatest-lower-bound predicate.
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, §3, displays (1)–(4), p.7

import Mathlib

namespace CompetitionComplexity

/-- **Feasibility for the program (1)–(4)**: constraints (2)–(4).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), §3, displays (2)–(4), p.7:
(2) `δⱼ₊₁ ≤ δⱼ` for every integer `j ≥ 0`; (3) `δⱼ² ≤ δⱼ₋₁ δⱼ₊₁` for every integer `j ≥ 1`;
(4) `δ₀ = 1` and `δⱼ > 0` for every integer `j ≥ 1`. -/
def Feasible (δ : ℕ → ℝ) : Prop :=
  (∀ j : ℕ, δ (j + 1) ≤ δ j) ∧
  (∀ j : ℕ, 1 ≤ j → δ j ^ 2 ≤ δ (j - 1) * δ (j + 1)) ∧
  δ 0 = 1 ∧
  (∀ j : ℕ, 1 ≤ j → 0 < δ j)

/-- The `i`-th term `(1 − (δᵢ₊₁/δᵢ)ⁿ) δᵢ` of the series in the objective (1), p.7. -/
noncomputable def tailTerm (n : ℕ) (δ : ℕ → ℝ) (i : ℕ) : ℝ :=
  (1 - (δ (i + 1) / δ i) ^ n) * δ i

/-- **The objective (1)**, §3, p.7:
`(1 + ε) Σ_{i=0}^{m−1} δᵢ − Σ_{i=0}^{∞} (1 − (δᵢ₊₁/δᵢ)ⁿ) δᵢ`.

**Formalization Note.** The infinite series is Lean's `tsum`, which is `0` on a non-summable
family. On every feasible `δ` (the only sequences the program considers) the terms are
nonnegative and bounded by `n(δᵢ − δᵢ₊₁)`, so the series is summable and `tsum` is its sum;
this is proved in the mission's verification file. The *value* of the program, an infimum that
is in general not attained, is never formed as a `sInf`: statements quantify over feasible `δ`
or use `IsGLB`. -/
noncomputable def objective (ε : ℝ) (n m : ℕ) (δ : ℕ → ℝ) : ℝ :=
  (1 + ε) * ∑ i ∈ Finset.range m, δ i - ∑' i, tailTerm n δ i

end CompetitionComplexity


