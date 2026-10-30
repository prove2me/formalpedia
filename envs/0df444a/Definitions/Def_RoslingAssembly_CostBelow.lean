-- Prove2me | Definitions.Def_RoslingAssembly_CostBelow
-- name    : RoslingAssembly_CostBelow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:42:34.094913+00:00
-- url     : https://prove2.me/theorems/85c6d2e9-d429-475a-86c7-341d534cbb3d
-- title:
--   The cost of problem P of a policy is below $K$
-- statement:
--   Let $0<\alpha\le1$ be the discount factor of problem P and $K$ a real number. A policy $\pi$ **has cost below $K$** if:
--   1. for $\alpha<1$: $\pi$ has finite discounted cost at $\alpha$ and $J_\alpha(\pi)<K$;
--   2. for $\alpha=1$: $\pi$ has finite discounted cost at every $\beta\in(0,1)$, its **average cost**
--   $$v=\lim_{\beta\to1^-}\frac{1-\beta}{\beta}\,J_\beta(\pi)$$
--   exists, and $v<K$.
--
--   The paper: "In the case where $\alpha=1$, the average cost per period is minimized instead of the total discounted cost. The average cost is constructed by multiplying (2) with the discount rate $(1-\alpha)/\alpha$ whereafter $\alpha\to1$."
--
--   **Formalization Note** Requiring the limit to exist is the strongest reading of the average cost. $(1-\beta)/\beta$ times the constant (4) tends to the paper's $\alpha=1$ constant $-\sum_ih_i\lambda(l_i+1)$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 567, (2)–(4)

import Mathlib
import Definitions.Def_RoslingAssembly_Admissible
import Definitions.Def_RoslingAssembly_discCost
open MeasureTheory Filter Topology

namespace RoslingAssembly

/-- **The cost of problem P of a policy is below K** (p. 567, (2)–(4)). Rosling, *Optimal
Inventory Policies for Assembly Systems under Random Demands*, Operations Research 37(4), 1989,
p. 567: "α = period discount factor, 0 < α ≤ 1." and "In the case where α = 1, the average cost
per period is minimized instead of the total discounted cost. The average cost is constructed by
multiplying (2) with the discount rate (1 − α)/α whereafter α → 1."

`CostBelow net ℓ H p μ Yh α pol K` says that the objective of problem P for `pol` is a
well-defined real number below `K`:
1. if `α < 1`: `pol` has finite discounted cost at `α` (`Admissible`) and `J_α(pol) < K`;
2. if `α = 1`: `pol` has finite discounted cost at every `β ∈ (0, 1)`, the average cost
   `v = lim_{β→1⁻} ((1 − β)/β) · J_β(pol)` exists, and `v < K`.

**Formalization Note.** At `α = 1` the constant (4) is `(1 − β)/β · K4 β`, whose limit is the
paper's `α = 1` line `− Σ_i h_i λ (l_i + 1)`. Requiring the limit to exist is the strongest
reading of "the average cost" (it implies the liminf and limsup readings). The `else` branch is
used only for `α = 1` (the theorems assume `0 < α ≤ 1`). -/
def CostBelow {N : ℕ} [NeZero N] (net : Network N) (ℓ : Fin N → ℕ) (H : Fin N → ℝ) (p : ℝ)
    (μ : Measure ℝ) (Yh : ℤ → Fin N → ℝ) (α : ℝ) (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) (K : ℝ) :
    Prop :=
  if α < 1 then
    Admissible net ℓ H p μ Yh pol α ∧ discCost net ℓ H p μ Yh pol α < K
  else
    ∃ v : ℝ, (∀ β ∈ Set.Ioo (0 : ℝ) 1, Admissible net ℓ H p μ Yh pol β) ∧
      Tendsto (fun β => (1 - β) / β * discCost net ℓ H p μ Yh pol β) (𝓝[<] 1) (𝓝 v) ∧ v < K

end RoslingAssembly


