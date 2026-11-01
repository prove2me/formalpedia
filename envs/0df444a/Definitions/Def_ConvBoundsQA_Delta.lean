-- Prove2me | Definitions.Def_ConvBoundsQA_Delta
-- name    : ConvBoundsQA_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:18.002753+00:00
-- url     : https://prove2.me/theorems/6d7770ec-5b41-4560-bc8c-d63ae0f4d0cf
-- title:
--   The simplex $\Delta_n$ with positive first component
-- statement:
--   For $n\in\mathbb N$,
--   $$
--   \Delta_n=\Bigl\{(\beta_0,\beta_1,\dots,\beta_n)\in(0,1)\times[0,1)^n:\ \sum_{i=0}^n\beta_i=1\Bigr\},
--   $$
--   the vectors of the standard $(n+1)$-simplex with positive first component. Scaled sets $c\Delta_n=\{c\beta:\beta\in\Delta_n\}$ parametrize the convolution bounds. The module also defines the variant $\Delta_n'$ in which $\beta_0\in(0,1]$ is allowed, used in the corrected statement of Theorem 1 so that its infimum contains $\beta=(t+s,0,\dots,0)$ as in (11) on p.8.
--
--   **Formalization Note** A point is a pair $(\beta_0,(\beta_1,\dots,\beta_n))$ with the second component in `Fin n → ℝ` (indices shifted to $0,\dots,n-1$); $c\Delta_n$ is the pointwise scalar multiple of the set.
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, §4, p.8; (11), p.8

import Mathlib

namespace ConvBoundsQA

/-- The set `Δₙ = {(β₀, β₁, …, βₙ) ∈ (0, 1) × [0, 1)ⁿ : Σ_{i=0}^n βᵢ = 1}`, the standard
`(n + 1)`-simplex with positive first component
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §4, p.8). Scaled sets `c • Δₙ` are written with the
pointwise scalar multiplication of sets.

**Formalization Note** A point `β` is a pair: `β.1 = β₀` and `β.2 i = β_{i+1}` for `i : Fin n`
(the page's indices `1, …, n` are `0, …, n − 1`). -/
def Delta (n : ℕ) : Set (ℝ × (Fin n → ℝ)) :=
  {β | β.1 ∈ Set.Ioo 0 1 ∧ (∀ i, β.2 i ∈ Set.Ico 0 1) ∧ β.1 + ∑ i, β.2 i = 1}

/-- The set `Δₙ` with the first component allowed to equal `1`:
`{(β₀, β₁, …, βₙ) ∈ (0, 1] × [0, 1)ⁿ : Σ_{i=0}^n βᵢ = 1}`. It is used only in the corrected
statement of Theorem 1, whose infimum must contain `β = (t + s, 0, …, 0)` as (11) on p.8 and the
proof on p.39 do (Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, (11), p.8; Theorem 1, p.9).

**Formalization Note** Same indexing as `Delta`. -/
def DeltaCorr (n : ℕ) : Set (ℝ × (Fin n → ℝ)) :=
  {β | β.1 ∈ Set.Ioc 0 1 ∧ (∀ i, β.2 i ∈ Set.Ico 0 1) ∧ β.1 + ∑ i, β.2 i = 1}

end ConvBoundsQA


