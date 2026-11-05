-- Prove2me | Definitions.Def_ReusableMatching_twoSeed
-- name    : ReusableMatching_twoSeed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:24.762749+00:00
-- url     : https://prove2.me/theorems/829e8360-550f-4937-bd04-a363d9171ce9
-- title:
--   The seed vector of the two-seed run $\mathrm{PR}(y^1,y^2)$
-- statement:
--   Fix an edge $(i,j)$ and all seeds except the two seeds of $i$ in the periods $k(j)-1$ and $k(j)$ (the paper's $Y_{-i,j}$). Write $y^1=y_i^{k(j)-1}$ and $y^2=y_i^{k(j)}$. The run $\mathrm{PR}(y^1,y^2)$ is Periodic Reranking with these two seeds and the other seeds fixed.
--
--   Here $Y_{-i,j}$ is represented by a full seed vector $Y$, and the seed vector of $\mathrm{PR}(y^1,y^2)$ is $Y$ with the coordinate $(i,k(j)-1)$ replaced by $y^1$ and the coordinate $(i,k(j))$ replaced by $y^2$.
--
--   **Formalization Note** The two coordinates are distinct, and $k(j)-1$ is always a period because of the dummy period.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, p.9; Y_{−i,j} defined on p.8

import Mathlib
import Definitions.Def_ReusableMatching_period
import Definitions.Def_ReusableMatching_seedMeasure

namespace ReusableMatching

/-- **The seed vector of `PR(y¹, y²)`** (arXiv:2110.07084v2, p.9): "fix an arbitrary edge `(i, j)`
and seed `Y_{−i,j}`. To simplify notation, let `y¹ = y_i^{k(j)−1}` and `y² = y_i^{k(j)}`. Further,
let `PR(y¹, y²)` denote the matching output by PR given seeds `y¹, y²` for `i` and with other seeds
fixed according to `Y_{−i,j}`." Here `Y_{−i,j}` is "the vector of all seeds except `y_i^{k(j)}` and
`y_i^{k(j)−1}`" (p.8).

`twoSeed I Y i j y¹ y²` is the seed vector `Y` with the seed of `i` in period `k(j) − 1` replaced by
`y¹` and the seed of `i` in period `k(j)` replaced by `y²`.

**Formalization Note.** `Y_{−i,j}` is represented by a full seed vector `Y` whose two coordinates
`(i, k(j) − 1)` and `(i, k(j))` are overwritten, so the run `PR(y¹, y²)` is the run of
`PeriodicReranking` at `twoSeed I Y i j y¹ y²`. The two coordinates are distinct, and `k(j) − 1`
is a genuine period because of the dummy period (`prevPeriod`). -/
def twoSeed {V : Type*} [DecidableEq V] {n : ℕ} (I : OBMRRInstance V n) (Y : Seeds V n)
    (i : V) (j : Fin n) (y1 y2 : unitInterval) : Seeds V n :=
  Function.update (Function.update Y (i, prevPeriod I j) y1) (i, period I j) y2

end ReusableMatching


