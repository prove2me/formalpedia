-- Prove2me | Definitions.Def_BewleyGE_IsCSE
-- name    : BewleyGE_IsCSE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:34:23.714242+00:00
-- url     : https://prove2.me/theorems/052b885d-2189-485e-9d61-d3c2399ddab4
-- title:
--   Competitive stationary equilibrium (Definition 1)
-- statement:
--   A **competitive stationary equilibrium** consists of prices $p\gg0$ and an interest rate $r\in(0,1)$, a savings policy $g$, a demand function $x^*$ (with value function $V$) and a wealth distribution $\mu\in\mathcal P(A(p,r))$ such that
--
--   1. $x^*$ is the demand function and $g$ satisfies (1);
--   2. $\mu=M\mu$;
--   3. every good market clears: for each good $i$,
--   $$
--   \int_{A(p,r)}x^*_i\big(a-g(a),p\big)\,\mu(da)=\sum_{y\in\mathcal Y}e(y)\,y_i ;
--   $$
--   4. the bond market clears: $\displaystyle\int_{A(p,r)}g(a)\,\mu(da)=0$.
--
--   **Formalization Note** The right side of 3 is the paper's $\sum_{y_i\in\mathcal Y_i}e_i(y_i)y_i$, written as the identity of p.24. The integrands of 3 and 4 are required to be integrable on $A(p,r)$, so the integrals are never junk.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Definition 1, pp.8–9; standing assumption of §2.1, p.7

import Mathlib
import Definitions.Def_BewleyGE_IsPartialEq

open MeasureTheory

namespace BewleyGE

/-- **Competitive stationary equilibrium** (CSE). Light, arXiv:1906.06810v2, Definition 1,
pp.8–9, with the standing assumption of §2.1 (p.7) that `p ≫ 0` and `r ∈ (0, 1)`.

Prices `(p, r)`, a savings policy `g`, a demand function `x*` and a wealth distribution
`μ ∈ P(A(p, r))` such that
(i) `g` satisfies (1) and `x*` is the demand (with `V` the value function);
(ii) `μ = Mμ`;
(iii) for each good `i`: `∫_{A(p,r)} x*ᵢ(a − g(a), p) μ(da) = ∑_{yᵢ ∈ 𝒴ᵢ} eᵢ(yᵢ) yᵢ`;
(iv) `∫_{A(p,r)} g(a) μ(da) = 0`.

**Formalization Note.** The marginal sum `∑_{yᵢ} eᵢ(yᵢ) yᵢ` is written `∑_{y ∈ 𝒴} e(y) yᵢ`, the
identity the paper uses on p.24. The integrands of (iii) and (iv) are required to be integrable
on `A(p, r)`, so the Bochner integral never takes its junk value `0`. The value function `V`
is an argument because (1) refers to it. -/
structure IsCSE {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ)
    (x : ℝ → Fin n → ℝ) (V g : ℝ → ℝ) (μ : Measure ℝ) : Prop where
  /-- `p ≫ 0`. -/
  p_pos : ∀ i, 0 < p i
  /-- `r > 0`. -/
  r_pos : 0 < r
  /-- `r < 1`. -/
  r_lt_one : r < 1
  /-- Definition 1 (i) and (ii). -/
  optimal_invariant : IsPartialEq E p r x V g μ
  /-- The demand for each good is integrable. -/
  goods_integrable : ∀ i, IntegrableOn (fun a => x (a - g a) i) (wealthSet E p r) μ
  /-- Definition 1 (iii): every good market clears. -/
  goods_clear : ∀ i,
    ∫ a in wealthSet E p r, x (a - g a) i ∂μ = ∑ y ∈ E.Y, E.e y * y i
  /-- Savings are integrable. -/
  savings_integrable : IntegrableOn g (wealthSet E p r) μ
  /-- Definition 1 (iv): the bond market clears. -/
  savings_clear : ∫ a in wealthSet E p r, g a ∂μ = 0

end BewleyGE


