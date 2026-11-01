-- Prove2me | Definitions.Def_CloudCostOpt_orderValue
-- name    : CloudCostOpt_orderValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:02:10.830764+00:00
-- url     : https://prove2.me/theorems/85c08bcf-6092-488b-b79b-4f45c10b4a37
-- title:
--   Optimal value $f_i(s,l)$ of the single-order problem $\hat{\mathbb P}_i$
-- statement:
--   Problem $\hat{\mathbb P}_i$: a single type-$i$ order is processed one period at a time; resource type $j\ge1$ can be hired on demand at $R_j$ per period, the dummy resource $0$ costs nothing, and the order pays $W_i$ in every period in which it is late. For an order in order-state $(s,l)$,
--
--   $$
--   f_i(s,l)=\inf_{\sigma}\ \mathbb E\Big[\sum_{n\ge0}\mathbb 1\big[l_n<L_i\big]\Big(R_{\sigma(h_n)}+W_i\,\mathbb 1[s+n\ge\delta_i]\Big)\Big],
--   $$
--
--   where $l_n$ is $l$ plus the number of successes among the first $n$ periods, and the infimum runs over all history-dependent strategies $\sigma$. The order leaves after its $L_i$-th step, so $f_i(s,L_i)=0$.
--
--   **Formalization Note** Strategies are deterministic functions of the outcome history; the expectation is a lower Lebesgue integral in $[0,\infty]$ with respect to i.i.d. uniforms.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.12 ("fᵢ(s, l) denote the minimum expected remaining cost for completing that order"; fᵢ(s, Lᵢ) := 0)

import Mathlib
import Definitions.Def_CloudCostOpt_orderOutcomes
import Definitions.Def_CloudCostOpt_resCost

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`fᵢ(s, l)`, the optimal value of problem `ℙ̂ᵢ`** from order-state `(s, l)`: the minimum, over
history-dependent strategies `σ`, of the expected total cost to complete a type-`i` order that is in
order-state `(s, l)`, when every resource `j ≥ 1` is hired on demand at `R_j` per period (`R₀ = 0`)
and the order pays `Wᵢ` in every period in which it is late (`s ≥ δᵢ`).  In the `n`-th period
from now the order is in state `(s + n, l + #successes so far)`; it leaves after its `Lᵢ`-th step.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.12 (`ℙ̂ᵢ`, "`fᵢ(s, l)` denote the minimum expected remaining cost for completing that
order", and `fᵢ(s, Lᵢ) := 0`).

Formalization Note: `l ≥ Lᵢ` gives `0`, the paper's `fᵢ(s, Lᵢ) := 0`.  The uniforms `U n` are i.i.d.
uniform on `[0, 1]`; expectations are lower integrals in `ℝ≥0∞`. -/
noncomputable def orderValue (S : System) (i : Fin S.I) (s l : ℕ) : ℝ≥0∞ :=
  ⨅ σ : List Bool → Fin (S.J + 1), ∫⁻ U, ∑' n : ℕ,
    (if l + (orderOutcomes S i σ U n).count true < S.L i then
      ENNReal.ofReal (resCost S (σ (orderOutcomes S i σ U n)) +
        (if S.δ i ≤ s + n then S.W i else 0))
    else 0) ∂(Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))

end CloudCostOpt


