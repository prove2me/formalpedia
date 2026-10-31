-- Prove2me | Definitions.Def_DissolveCDF_rhoX
-- name    : DissolveCDF_rhoX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:46.51127+00:00
-- url     : https://prove2.me/theorems/5bbc4c15-664e-4673-9842-3301138df1dc
-- title:
--   §2.3 — the radius $\rho_x$
-- statement:
--   For $x\in\mathcal M$, the paper defines the positive scalar $\rho_x\le1$ by
--
--   $$
--   \rho_x:=\operatorname*{argmax}_{0<\rho\le1}\ \rho\quad\text{s.t.}\quad \inf\{\sigma_{\min}(J_c(y)) : y\in\mathbb R^n,\ \|y-x\|\le\rho\}\ \ge\ \tfrac12\,\sigma_{\min}(J_c(x)),
--   $$
--
--   and sets $\Theta_x:=\{y\in\mathbb R^n:\|y-x\|\le\rho_x\}$. On $\Theta_x$ the constraint gradients stay uniformly independent: $\sigma_{\min}(J_c(y))\ge\frac12\sigma_{x,c}$.
--
--   **Formalization Note** The argmax is encoded as the supremum of the feasible $\rho\in(0,1]$, and the condition on the infimum is written pointwise for every $y$ with $\|y-x\|\le\rho$. Under Assumption 1.1 the feasible set is an interval $(0,\rho^*]$ containing its right end, so the supremum is the paper's argmax.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.3, p.7

import Mathlib
import Definitions.Def_DissolveCDF_transJac
import Definitions.Def_DissolveCDF_sigmaMin
import Definitions.Def_DissolveCDF_sigmaXC

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7): for `x ∈ M`, the positive scalar `ρ_x ≤ 1`,
`ρ_x := argmax_{0<ρ≤1} ρ  s.t.  inf {σ_min(J_c(y)) : y ∈ ℝⁿ, ‖y − x‖ ≤ ρ} ≥ ½ σ_min(J_c(x))`.

**Formalization Note** The argmax is encoded as the supremum (`sSup`) of the feasible `ρ ∈ (0, 1]`.
The condition "inf over the closed ball `≥ ½σ_{x,c}`" is written pointwise: every `y` with
`‖y − x‖ ≤ ρ` has `σ_min(J_c(y)) ≥ ½σ_{x,c}`. Under Assumption 1.1 `y ↦ σ_min(J_c(y))` is
continuous and `σ_{x,c} > 0` for `x ∈ M`, so the feasible set is a nonempty interval `(0, ρ*]`
containing its right end, and the supremum is the paper's argmax. -/
noncomputable def rhoX {n p : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {ρ : ℝ | 0 < ρ ∧ ρ ≤ 1 ∧
    ∀ y : EuclideanSpace ℝ (Fin n), ‖y - x‖ ≤ ρ → 1 / 2 * sigmaXC c x ≤ sigmaMin (transJac c y)}

end DissolveCDF


