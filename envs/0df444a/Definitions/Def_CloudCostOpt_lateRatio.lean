-- Prove2me | Definitions.Def_CloudCostOpt_lateRatio
-- name    : CloudCostOpt_lateRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:59.349193+00:00
-- url     : https://prove2.me/theorems/5349f9ce-0b70-4b40-b399-99d86f3e695d
-- title:
--   Per-step cost $\min_j (R_j+W_i)/\beta_{i,j}$ of a late order
-- statement:
--   For an order type $i$,
--
--   $$
--   c_i^{Late}=\min_{j:\ \beta_{i,j}>0}\frac{R_j+W_i}{\beta_{i,j}},
--   $$
--
--   the minimal expected cost per completed step of a late order (Lemma 1).
--
--   **Formalization Note** On the page, $(R_0+W_i)/\beta_{i,0}=W_i/0=+\infty$, so the dummy resource never attains the minimum; in Lean $x/0=0$, so the minimum is restricted to $\{j:\beta_{i,j}>0\}$. This set is finite and, under the standing assumptions, nonempty, so the real infimum is the minimum.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, Lemma 1, p.12

import Mathlib
import Definitions.Def_CloudCostOpt_resCost

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`min_j (R_j + Wᵢ)/β_{i,j}`**, the per-step cost of a late type-`i` order on its best
resource (Lemma 1), the minimum taken over the resources with `β_{i,j} > 0`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, Lemma 1, p.12.

Formalization Note: on the page `(R₀ + Wᵢ)/β_{i,0} = Wᵢ/0 = +∞`, so the dummy resource never
attains the minimum; in Lean `x / 0 = 0`, so the minimum is restricted to `{j | 0 < β_{i,j}}`, which
is nonempty under `Standing`. -/
noncomputable def lateRatio (S : System) (i : Fin S.I) : ℝ :=
  ⨅ j : {j : Fin (S.J + 1) // 0 < S.β i j}, (resCost S j + S.W i) / S.β i j

end CloudCostOpt


