-- Prove2me | Definitions.Def_BewleyGE_Assumption1
-- name    : BewleyGE_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:29.959431+00:00
-- url     : https://prove2.me/theorems/ef95cf9b-749f-4c0c-8987-a2aba5b40a88
-- title:
--   Assumption 1 on the utility function
-- statement:
--   The utility $U$ of an economy satisfies **Assumption 1** when:
--
--   1. $U$ is strictly increasing on $\mathbb R^n_+$: if $x'\le x$ coordinatewise and $x'\ne x$, then $U(x')<U(x)$;
--   2. $U$ is continuous on $\mathbb R^n_+$ and continuously differentiable on the open orthant $\mathbb R^n_{++}$;
--   3. $U$ is strictly concave on $\mathbb R^n_+$;
--   4. $\partial U(0)/\partial x_j=\infty$ for some good $j$, in the sense that $\dfrac{U(te_j)-U(0)}{t}\to+\infty$ as $t\downarrow0$;
--   5. for every $p\gg0$ the indirect utility $u_p(c)=\max_{x\in X(c,p)}U(x)$ ($c\ge0$; the maximum is attained) is continuously differentiable on $(0,\infty)$ and satisfies the Inada conditions
--   $$
--   \lim_{c\to\infty}u_p'(c)=0,\qquad \lim_{c\to0^+}u_p'(c)=\infty .
--   $$
--
--   Items 1–4 are Assumption 1(i) and item 5 is Assumption 1(ii) of the paper. The CES utility $U(x)=\sum_i\alpha_ix_i^\gamma$ with $\alpha_i>0$, $0<\gamma<1$ is the paper's example.
--
--   **Formalization Note** The paper writes "$x>x'$" without defining it; it is read as $x\ge x'$ and $x\ne x'$. "Continuously differentiable" cannot hold on the closed orthant together with $\partial U(0)/\partial x_j=\infty$, so it is read on the open orthant, with continuity on the closed one; likewise $u_p$ is $C^1$ on $(0,\infty)$, where its Inada limits live.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Assumption 1, p.6 (definitions of increasing and strictly increasing on the same page)

import Mathlib
import Definitions.Def_BewleyGE_Economy
import Definitions.Def_BewleyGE_budget

open Filter Topology

namespace BewleyGE

/-- **Assumption 1.** Light, arXiv:1906.06810v2, Assumption 1, p.6.

(i) `U` is strictly increasing, continuously differentiable, strictly concave, and
`∂U(0)/∂xⱼ = ∞` for some `j`.
(ii) For every `p ≫ 0` the indirect utility `u_p(c) = U(x*(c, p))` is continuously differentiable
and satisfies `lim_{c→∞} u_p'(c) = 0` and `lim_{c→0} u_p'(c) = ∞`.

**Formalization Note.**
* "Strictly increasing" uses the page's definition "x > x′ implies U(x) > U(x′)" with `x > x′`
  read as `x ≥ x′` coordinatewise and `x ≠ x′` (reading R3), for bundles in `ℝⁿ₊`.
* "Continuously differentiable" is read as: `U` is continuous on the closed orthant `ℝⁿ₊` and
  `C¹` on the open orthant (reading R2); a closed-orthant `C¹` reading is incompatible with
  `∂U(0)/∂xⱼ = ∞`. That clause is the right difference quotient `(U(t eⱼ) − U(0))/t → +∞` as
  `t ↓ 0`.
* In (ii) the indirect utility is the function `u` whose value at every `c ≥ 0` is the greatest
  value of `U` on the budget plane `X(c, p)` (so the maximum is attained, as `x*` is the
  argmax); it is `C¹` on `(0, ∞)`, where the Inada limits are taken. -/
structure Assumption1 {n : ℕ} (E : Economy n) : Prop where
  /-- (i) `U` is strictly increasing on `ℝⁿ₊`: `x′ ≤ x`, `x′ ≠ x` imply `U x′ < U x`. -/
  strictMono : ∀ x x' : Fin n → ℝ, (∀ i, 0 ≤ x' i) → x' ≤ x → x' ≠ x → E.U x' < E.U x
  /-- (i) `U` is continuous on the closed orthant. -/
  continuousOn : ContinuousOn E.U {x | ∀ i, 0 ≤ x i}
  /-- (i) `U` is continuously differentiable on the open orthant. -/
  contDiffOn : ContDiffOn ℝ 1 E.U {x | ∀ i, 0 < x i}
  /-- (i) `U` is strictly concave on `ℝⁿ₊`. -/
  strictConcaveOn : StrictConcaveOn ℝ {x | ∀ i, 0 ≤ x i} E.U
  /-- (i) `∂U(0)/∂xⱼ = ∞` for some good `j`. -/
  partial_zero : ∃ j : Fin n,
    Tendsto (fun t : ℝ => (E.U (Pi.single j t) - E.U 0) / t) (𝓝[>] 0) atTop
  /-- (ii) For every `p ≫ 0` the indirect utility is `C¹` on `(0, ∞)` and satisfies the Inada
  conditions. -/
  indirect : ∀ p : Fin n → ℝ, (∀ i, 0 < p i) → ∃ u : ℝ → ℝ,
    (∀ c, 0 ≤ c → IsGreatest (E.U '' budget p c) (u c)) ∧
    ContDiffOn ℝ 1 u (Set.Ioi 0) ∧
    Tendsto (deriv u) atTop (𝓝 0) ∧
    Tendsto (deriv u) (𝓝[>] 0) atTop

end BewleyGE


