-- Prove2me | Definitions.Def_OceanPlastic_Problem4
-- name    : OceanPlastic_Problem4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:29.156179+00:00
-- url     : https://prove2.me/theorems/b99a3cd2-c0dd-4af6-b294-da11be89c137
-- title:
--   Problem (4) and its no-additionality variant: feasibility and optimal solutions; $d^O_o(r)$ and $\hat p_m$
-- statement:
--   The firm's problem (4) with additionality is
--   $$\max_{d_o,r}\ T^O(d_o,r)\quad\text{s.t.}\quad V^O(r)-V^B\ge d_o,\quad 0\le d_o\le Q_o,\quad r\ge0.$$
--   The first constraint is **additionality**: the firm may sell only as many offsets as the recycling volume it adds over the benchmark. In the **no-additionality variant** that constraint is replaced by $V^O(r)\ge d_o$: the firm may sell offsets on all the plastic recycled.
--
--   A pair $(r,d_o)$ is an **optimal solution** of either problem if it is feasible and no feasible pair has a larger value of $T^O$.
--
--   The module also records the offset sales volume of Proposition 2(a) and the price threshold of Corollary 3,
--   $$d^O_o(r)=\min\Bigl\{\frac{Q_o(\bar v_o+\delta_o r)}{2\bar v_o},\,Q_o,\,\frac{Mr}{2k}\Bigr\},\qquad \hat p_m=\frac{kQ_o\bar v_o}{(1-\delta_o)kQ_o+M\bar v_o}.$$
--
--   **Formalization Note** The module declares `Feasible`, `FeasibleNoAdd`, `IsOptimal`, `IsOptimalNoAdd`, `dO`, `pHat` in the namespace `OceanPlastic.Params`. The price condition of (1) is equivalent to $0\le d_o\le Q_o$. The paper poses (4) in the total bonus $r$, and so does this definition.
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, eq. (4), p.11; §5, p.18; Proposition 2(a), p.15; Corollary 3, p.35

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark
import Definitions.Def_OceanPlastic_CaseO

namespace OceanPlastic

namespace Params

/-- **Feasible set of problem (4)** (the firm with additionality). `(r, d_o)` is feasible iff
`V^O(r) − V^B ≥ d_o`, `0 ≤ d_o ≤ Q_o` and `r ≥ 0`. Baron–Romero–Zhang–Zhou, MSOM,
doi:10.1287/msom.2022.0643, eq. (4), p. 11.

**Formalization Note** The price condition `(p_o − δ_o r) / v̄_o ∈ [0, 1]` of (1) is equivalent to
`0 ≤ d_o ≤ Q_o`, so it adds no constraint. The paper poses (4) in the total bonus `r`, with `V^O`,
`Π^O_C`, `Π^O_P` given by (3), and so does this definition; `eq_3` records the domain
`r_c ≤ p_m + r_p` on which (3) is the lower stages' equilibrium. -/
def Feasible (P : Params) (r d : ℝ) : Prop :=
  P.VO r - P.VB ≥ d ∧ 0 ≤ d ∧ d ≤ P.Q ∧ 0 ≤ r

/-- **Feasible set of the no-additionality variant of problem (4)**: the first constraint becomes
`V^O(r) ≥ d_o`. §5, p. 18 ("the firm can sell plastic offsets associated with all the plastic
recycled in Case O, i.e., V̂^O(r̂) ≥ d̂_o") and the proof of Corollary 3, p. 46. -/
def FeasibleNoAdd (P : Params) (r d : ℝ) : Prop :=
  P.VO r ≥ d ∧ 0 ≤ d ∧ d ≤ P.Q ∧ 0 ≤ r

/-- **Optimal solution of problem (4)** with weights `ρ₁, ρ₂, ρ₃`: a feasible `(r, d_o)` that
maximizes `T^O` over the feasible set, eq. (4), p. 11. The firm's for-profit problem of §5 is the
case `ρ₁ = 1`, `ρ₂ = ρ₃ = 0`. -/
def IsOptimal (P : Params) (ρ₁ ρ₂ ρ₃ r d : ℝ) : Prop :=
  P.Feasible r d ∧ ∀ r' d', P.Feasible r' d' → P.TO ρ₁ ρ₂ ρ₃ d' r' ≤ P.TO ρ₁ ρ₂ ρ₃ d r

/-- **Optimal solution of the no-additionality variant of problem (4)**: a feasible `(r, d_o)` that
maximizes `T^O` over the feasible set of `FeasibleNoAdd`; §5, p. 18, and Corollary 3, p. 35. -/
def IsOptimalNoAdd (P : Params) (ρ₁ ρ₂ ρ₃ r d : ℝ) : Prop :=
  P.FeasibleNoAdd r d ∧ ∀ r' d', P.FeasibleNoAdd r' d' → P.TO ρ₁ ρ₂ ρ₃ d' r' ≤ P.TO ρ₁ ρ₂ ρ₃ d r

/-- **The offset sales volume at bonus `r`**:
`d^O_o(r) = min {Q_o (v̄_o + δ_o r) / (2 v̄_o), Q_o, M r / (2k)}`, Proposition 2(a), p. 15. -/
noncomputable def dO (P : Params) (r : ℝ) : ℝ :=
  min (min (P.Q * (P.vbar + P.δ * r) / (2 * P.vbar)) P.Q) (P.M * r / (2 * P.k))

/-- **The price threshold of Corollary 3**:
`p̂_m = k Q_o v̄_o / ((1 − δ_o) k Q_o + M v̄_o)`, p. 35. The denominator is positive. -/
noncomputable def pHat (P : Params) : ℝ :=
  P.k * P.Q * P.vbar / ((1 - P.δ) * P.k * P.Q + P.M * P.vbar)

end Params

end OceanPlastic


