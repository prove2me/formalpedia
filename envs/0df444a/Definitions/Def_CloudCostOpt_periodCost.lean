-- Prove2me | Definitions.Def_CloudCostOpt_periodCost
-- name    : CloudCostOpt_periodCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:07:12.903476+00:00
-- url     : https://prove2.me/theorems/e713a888-24e4-4c7f-9834-52c1ce7612bb
-- title:
--   Cost $C_t$ of a period in $\mathbb P(\mathbf A,\mathbf B)$
-- statement:
--   For reserved prices $\mathbf A=(A_j)$ and on-demand prices $\mathbf B=(B_j)$, the cost of period $t$ under $\pi$ is
--
--   $$
--   C_t^{\pi}=\sum_{j=1}^{J}\big(A_j M_j^{\pi}+B_j m_{j,t}^{\pi}\big)+\sum_{i=1}^{I}\sum_{s=\delta_i}^{t-2}\sum_{l=0}^{L_i-1}W_i\,x^{\pi}_{i,t}(s,l).
--   $$
--
--   The paper's cost is the case $\mathbf A=\mathbf R$, $\mathbf B=\mathbf V$; the relaxation $\mathbb P_{LB}$ of §3 is $\mathbf A=\mathbf B=\mathbf R$.
--
--   **Formalization Note** Valued in $[0,\infty]$ (`ENNReal.ofReal` of the prices).
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.5 (Costs; Note on P(A, B))

import Mathlib
import Definitions.Def_CloudCostOpt_stateAt

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The cost `C_t` of period `t = n + 1`** with reserved prices `A` and on-demand prices `B`:
`Σ_j (A_j M_j + B_j m_{j,t}) + Σ_i Σ_{s=δᵢ}^{t−2} Σ_{l=0}^{Lᵢ−1} Wᵢ x_{i,t}(s, l)`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.5 ("Costs"), and p.5 "Note" (the problem `ℙ(A, B)` for arbitrary cost vectors).

Formalization Note: the cost is valued in `ℝ≥0∞` (`ENNReal.ofReal` of the nonnegative prices);
`s` runs over `δᵢ ≤ s < n`, i.e. `δᵢ ≤ s ≤ t − 2`. -/
noncomputable def periodCost (S : System) (A B : Fin S.J → ℝ) (π : Policy S) (ω : Omega S)
    (n : ℕ) : ℝ≥0∞ :=
  ∑ j, (ENNReal.ofReal (A j) * (π.M j : ℝ≥0∞) +
      ENNReal.ofReal (B j) * (π.m n (history S π ω n) j : ℝ≥0∞)) +
    ∑ i, ∑ s ∈ Finset.Ico (S.δ i) n, ∑ l ∈ Finset.range (S.L i),
      ENNReal.ofReal (S.W i) * (stateAt S π ω n i s l : ℝ≥0∞)

end CloudCostOpt


