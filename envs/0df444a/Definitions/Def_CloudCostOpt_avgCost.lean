-- Prove2me | Definitions.Def_CloudCostOpt_avgCost
-- name    : CloudCostOpt_avgCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:08:31.095551+00:00
-- url     : https://prove2.me/theorems/f864ce15-6e1e-4933-a063-2da6df25b3cc
-- title:
--   Long-run average expected cost $f^\pi$
-- statement:
--   The **long-run average expected cost** of a policy $\pi$ in $\mathbb P(\mathbf A,\mathbf B)$ with arrival rates $\lambda$ is
--
--   $$
--   f^{\pi}=\liminf_{T\to\infty}\frac1T\sum_{t=1}^{T}\mathbb E\big[C_t^{\pi}\big].
--   $$
--
--   **Formalization Note** Expectations are lower Lebesgue integrals of the nonnegative costs, so no integrability side condition can make a cost vanish. The paper writes $\lim$ and asserts that it exists for stable policies; where it exists, $\liminf$ is the same number, and otherwise it is the smaller value, so optimal values can only fall and the gap bounds of the mission only get stronger.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.5 (Performance Measure)

import Mathlib
import Definitions.Def_CloudCostOpt_periodCost
import Definitions.Def_CloudCostOpt_sampleMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The long-run average expected cost `f^π`** of `π` in `ℙ(A, B)` with arrival rates `lam`:
`liminf_{T→∞} (Σ_{t=1}^T E[C_t^π]) / T`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.5 ("Performance Measure").

Formalization Notes:
* expectations are lower Lebesgue integrals of the nonnegative costs (`ℝ≥0∞`), so no integrability
  side condition can make a cost vanish;
* the paper writes `lim`; for a stable policy it asserts the limit exists, and then `liminf` is the
  same number.  Where it does not exist, `liminf` is the smaller value, so infima can only fall and
  the gap bounds of the mission only get stronger (reading). -/
noncomputable def avgCost (S : System) (A B : Fin S.J → ℝ) (lam : Fin S.I → ℝ≥0)
    (π : Policy S) : ℝ≥0∞ :=
  Filter.liminf (fun T : ℕ =>
    (∑ n ∈ Finset.range T, ∫⁻ ω, periodCost S A B π ω n ∂(sampleMeasure S lam)) / (T : ℝ≥0∞))
    Filter.atTop

end CloudCostOpt


