-- Prove2me | Definitions.Def_RoslingAssembly_K4
-- name    : RoslingAssembly_K4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:40:33.270823+00:00
-- url     : https://prove2.me/theorems/078746ce-f748-48fa-a777-4b97e43c1310
-- title:
--   The constant (4) of the objective, $\alpha<1$
-- statement:
--   The objective (2) carries the constant
--   $$-\sum_{i=1}^N h_i\,\lambda\,(l_i+1)\,\frac{\beta^{l_i}}{1-\beta}\qquad(\beta<1), \tag{4}$$
--   where $\lambda=\mathbb E[\xi_t]$ is the mean demand. It collects the expected demands that the echelon formulation subtracts.
--
--   **Formalization Note** Only the line $\alpha<1$ of (4) is defined; the line $\alpha=1$, $-\sum_ih_i\lambda(l_i+1)$, is its limit after multiplication by $(1-\beta)/\beta$, which is how the average cost is formed. The formula is only used for $\beta<1$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 567, (4)

import Mathlib
import Definitions.Def_RoslingAssembly_Network_h
open MeasureTheory

namespace RoslingAssembly

/-- **The constant of (2)**, equation (4) for α < 1 (p. 567). Rosling, *Optimal Inventory
Policies for Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 567:
"The last constant in (2) (and its average cost analog) equals − Σ_{i=1}^N h_i · λ · (l_i + 1)
α^{l_i}/(1 − α) if α < 1 … (4)"; p. 566: "λ = E(ξ_t), the expected value of ξ_t, λ > 0".

For a discount factor `β`, `K4 net ℓ H μ β = − Σ_i h_i λ (l_i + 1) β^{l_i}/(1 − β)` with
`λ = ∫ ξ dμ` the mean one-period demand.

**Formalization Note.** Only the `α < 1` line of (4) is defined; the `α = 1` line is its limit
after multiplying by `(1 − β)/β` and letting `β → 1⁻`, which is how the average cost is built
(`CostBelow`). At `β = 1` the formula divides by zero (Lean's `x / 0 = 0`); it is only used for
`β < 1`. -/
noncomputable def K4 {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (H : Fin N → ℝ) (μ : Measure ℝ)
    (β : ℝ) : ℝ :=
  -∑ i, net.h H i * (∫ x, x ∂μ) * ((ℓ i : ℝ) + 1) * β ^ ℓ i / (1 - β)

end RoslingAssembly


