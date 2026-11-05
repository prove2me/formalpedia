-- Prove2me | Definitions.Def_ReusableMatching_criticalThreshold
-- name    : ReusableMatching_criticalThreshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:37.568202+00:00
-- url     : https://prove2.me/theorems/705af677-69ac-4634-9f37-ac105e881ee3
-- title:
--   The critical threshold $y^c_t(y^1)$
-- statement:
--   Fix an edge $(i,j)$ and the seeds $Y_{-i,j}$. For $y^1\in[0,1]$ and an arrival $t$, let
--
--   $$
--   M_t(y^1)=\max_{v\in S_t(y^1,1),\ (v,t)\in E} r_v\bigl(1-g(y_v^{k(t)})\bigr)
--   $$
--
--   be the largest reduced price among the available neighbours of $t$ in the run $\mathrm{PR}(y^1,1)$, with $M_t(y^1)=0$ when there is no such neighbour. The **critical threshold** $y^c_t(y^1)$ is the solution $y\in[0,1]$ of
--
--   $$
--   r_i\bigl(1-g(y)\bigr)=M_t(y^1),
--   $$
--
--   and $0$ if there is no solution. Setting $y^2=1$ makes the reduced price of $i$ in period $k(j)$ equal to $0$, so $M_t(y^1)$ is the best price at $t$ when $i$ is effectively removed in period $k(j)$.
--
--   **Formalization Note** The threshold is $\sup\{y\in[0,1]: M_t(y^1)\le r_i(1-g(y))\}$, and $0$ when this set is empty. For $r_i>0$ and $\beta>0$, $y\mapsto r_i(1-g(y))$ is continuous and strictly decreasing on $[0,1]$, so this is the unique solution when one exists and $0$ otherwise.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, p.9

import Mathlib
import Definitions.Def_ReusableMatching_availableSet
import Definitions.Def_ReusableMatching_twoSeed

namespace ReusableMatching

/-- **The critical threshold `y^c_t(y¹)`** of the analysis of Periodic Reranking for the edge
`(i, j)` (arXiv:2110.07084v2, p.9): "Given `y¹ ∈ [0, 1]`, for every arrival `t ∈ U`, define the
critical threshold `y^c_t(y¹)` as the solution to,
`r_i (1 − g(y^c_t(y¹))) = max_{v ∈ S_t(y¹,1), (v,t) ∈ E} r_v (1 − g(y_v^{k(t)}))`.
Due to the monotonicity of function `g`, there is at most one solution to this equation. If there
is no solution, we let `y^c_t(y¹) = 0`."

Writing `M` for the right-hand side (the largest reduced price among the available neighbours of
`t` in the run `PR(y¹, 1)`), `criticalThreshold I β Y i j y¹ t` is
`sup { y ∈ [0, 1] : M ≤ r_i (1 − g(y)) }`, and `0` when this set is empty.

**Formalization Note.**
* The run is `PR(y¹, 1)`: the seed vector is `twoSeed I Y i j y¹ 1`, and the reduced prices
  `r_v (1 − g(y_v^{k(t)}))` are read from that vector. The maximum includes `v = i` when `i` is an
  available neighbour of `t`, as printed.
* The maximum over an empty set of neighbours is `0` (an unmatched arrival has dual `0`, p.8).
* For `r_i > 0` and `β > 0` the map `y ↦ r_i (1 − g(y))` is continuous and strictly decreasing on
  `[0, 1]`, from `r_i (1 − e^{−β})` to `0`, and `M ≥ 0`. So the set is `[0, y*]` when the equation
  has the solution `y*` (and the supremum is that solution), and empty when it has none (and the
  value is `0`), which is the paper's definition. For `r_i = 0` the value is `1` or `0`; every
  statement that uses it then has a factor `r_i = 0` or compares two thresholds of the same kind. -/
noncomputable def criticalThreshold {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j : Fin n) (y1 : unitInterval)
    (t : Fin n) : ℝ := by
  classical
  exact
    let Y' := twoSeed I Y i j y1 1
    let C := (availableSet I β Y' t).filter (fun v => (v, t) ∈ I.E)
    let M : ℝ := if h : C.Nonempty then C.sup' h (fun v => reducedPrice I β Y' v t) else 0
    sSup {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ M ≤ I.r i * (1 - g β y)}

end ReusableMatching


