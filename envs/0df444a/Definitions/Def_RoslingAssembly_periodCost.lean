-- Prove2me | Definitions.Def_RoslingAssembly_periodCost
-- name    : RoslingAssembly_periodCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:39:26.423397+00:00
-- url     : https://prove2.me/theorems/fccb8bc2-ebd2-40aa-b20f-62b1b75adaad
-- title:
--   Cost of period $t$ in problem P
-- statement:
--   For a discount factor $\beta$, the cost of period $t$ in problem P is the bracket of (2),
--   $$c_t=\sum_{i=1}^N\beta^{l_i}h_iY_{it}+\beta^{l_1}(p+H_1)\,G_{l_1}(Y_{1t}),$$
--   where $h_i$ are the echelon holding costs, $H_1$ is the installation holding cost of the end item, $p$ is the backlog cost per unit and period, and $G_{l_1}$ is the expected backlog function. The holding cost incurred for item $i$ in period $t+l_i$ and the backlog cost of period $t+l_1$ are accounted for in period $t$.
--
--   **Formalization Note** The end item is Lean item $0$. $p$ and $H$ are arbitrary reals.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 567, Problem P, (2)

import Mathlib
import Definitions.Def_RoslingAssembly_Network_h
import Definitions.Def_RoslingAssembly_Ypath
import Definitions.Def_RoslingAssembly_backlogG
open MeasureTheory

namespace RoslingAssembly

/-- **Cost of period t in problem P** (p. 567, (2)). Rosling, *Optimal Inventory Policies for
Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 567, Problem P:
"Min_Y E{ Σ_{t=1}^∞ α^{t−1} ( Σ_{i=1}^N α^{l_i} · h_i · Y_it + α^{l_1}(p + H_1)
∫_{Y_1t}^∞ (ξ − Y_1t) φ_1^{l_1+1}(ξ) dξ ) } + constant (2)"; p. 567: "p = unit backlogging cost
per period of the end item; α = period discount factor".

For a discount factor `β`, `periodCost net ℓ H p μ Yh pol β ω t` is the bracket of (2) in period
`t` along the demand path `ω`:
$$\sum_i \beta^{l_i}h_iY_{it}+\beta^{l_1}(p+H_1)\,G_{l_1}(Y_{1t}),$$
with `h` the echelon holding costs, `H_1` the end item's installation holding cost and `G` the
expected backlog function `backlogG μ l_1`.

**Formalization Note.** Items are `Fin N`, 0-based: the end item (paper item 1) is Lean item `0`,
so `H_1`, `l_1`, `Y_1t` are `H 0`, `ℓ 0`, `Y 0`. Periods are integers with the paper's numbering.
`p` and `H` are arbitrary reals. -/
noncomputable def periodCost {N : ℕ} [NeZero N] (net : Network N) (ℓ : Fin N → ℕ)
    (H : Fin N → ℝ) (p : ℝ) (μ : Measure ℝ) (Yh : ℤ → Fin N → ℝ)
    (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) (β : ℝ) (ω : ℕ → ℝ) (t : ℤ) : ℝ :=
  ∑ i, β ^ ℓ i * net.h H i * Ypath Yh pol ω t i +
    β ^ ℓ 0 * (p + H 0) * backlogG μ (ℓ 0) (Ypath Yh pol ω t 0)

end RoslingAssembly


