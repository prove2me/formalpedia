-- Prove2me | Definitions.Def_NonlinearPriority_IsLongRunAvgCost
-- name    : NonlinearPriority_IsLongRunAvgCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:21.947255+00:00
-- url     : https://prove2.me/theorems/f9daf997-449f-45f3-8f67-7e9e4086c644
-- title:
--   Long-run average waiting cost $C^\pi$, (1)
-- statement:
--   With waiting-cost functions $C_i$, the long-run average cost of a policy $\pi$ is
--   $$C^\pi\equiv\lim_{t\to\infty}\frac{1}{t}\sum_{i=1}^K\sum_{k=1}^{n_i(t)}C_i\bigl(V^{\pi,x_0}_{i,k}\bigr),\tag{1}$$
--   where $n_i(t)$ is the number of type-$i$ arrivals by time $t$. A real number $c$ is the long-run average cost of $\pi$ if, for every initial state $x_0$, the average in (1) converges to $c$ almost surely.
--
--   **Formalization Note** The double sum is written as one sum over the arrivals with arrival time at most $t$, each with its own type's cost; initial customers are not arrivals. The sum is a `finsum`, which would be $0$ if infinitely many arrivals occurred by time $t$, an event of probability zero.
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, (1), p.4 (PDF 5)

import Mathlib
import Definitions.Def_NonlinearPriority_IsSteadyStateLaw

open MeasureTheory Filter Topology

namespace NonlinearPriority

variable {K : ℕ} {P : Params K} {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}

/-- The average in (1) at time `t`: the sum of the waiting costs `C_{Y n}(V n)` of the arrivals
`n` with arrival time `≤ t`, divided by `t`. -/
noncomputable def avgCost (X : Inputs P Ω Pr) (C : Fin K → ℝ → ℝ) (x0 : InitState K)
    (ord : Fin K → ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  (∑ᶠ n ∈ {n : ℕ | arrTime (X.realize ω) n ≤ t},
      C (X.Y n ω) (waitingTime x0 (X.realize ω) ord n)) / t

/-- **`c` is the long-run average cost (1) of the policy `ord`** (p. 4, PDF 5). Ouyang, Argon and
Ziya, Management Science (2021), doi:10.1287/mnsc.2020.3952:

`C^π ≡ lim_{t→∞} Σ_{i=1}^K Σ_{k=1}^{n_i(t)} C_i(V^{π,x0}_{i,k}) / t` (whenever the limit exists).

Here: for every initial state `x0`, almost surely, the average `avgCost` converges to `c` as
`t → ∞` (over the reals).

**Formalization Note.**
* The double sum of (1) over types `i` and type-`i` arrivals `k ≤ nᵢ(t)` is the sum over all
  arrivals with arrival time `≤ t`, each with its own type's cost; initial customers are not
  arrivals and are not counted.
* The paper's `C^π` does not carry `x0` and the limit is random; the reading here is the constant
  limit, almost surely, from every initial state (what §A.2.1 proves).
* The sum is a `finsum`; it would be `0` if infinitely many arrivals happened by time `t`, which
  has probability zero. -/
def IsLongRunAvgCost (X : Inputs P Ω Pr) (C : Fin K → ℝ → ℝ) (ord : Fin K → ℕ) (c : ℝ) : Prop :=
  ∀ x0 : InitState K, ∀ᵐ ω ∂Pr, Tendsto (avgCost X C x0 ord ω) atTop (𝓝 c)

end NonlinearPriority


