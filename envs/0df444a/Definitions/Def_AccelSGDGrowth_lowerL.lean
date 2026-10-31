-- Prove2me | Definitions.Def_AccelSGDGrowth_lowerL
-- name    : AccelSGDGrowth_lowerL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:33.750035+00:00
-- url     : https://prove2.me/theorems/93fce149-4166-4057-80e3-35cf96f10fb2
-- title:
--   The lower bound $L_k$ of (4.3)
-- statement:
--   Given $f$, $m$, weights $a_i$, iterates $x_i$, vectors $g_i$ and a point $x_\star$, write $\varepsilon_i=g_i-\nabla f(x_i)$ and $z_{k+1}=-\sum_{i=1}^k a_ig_i$. The lower bound of (4.3) is
--   $$
--   L_{k+1}=\frac1{A_k}\sum_{i=1}^k a_i\big[f(x_i)-\varepsilon_i^\top(x_\star-x_i)\big]-\frac1{A_k}\phi_k^\star(z_{k+1})-\frac1{A_k}\sum_{i=1}^k a_ig_i^\top x_i .
--   $$
--   By Lemma 4.1(c), $f(x_\star)\ge L_{k+1}$ for $f\in\mathcal F(m,\mathcal L)$ with minimizer $x_\star$. It is the lower half of the duality-gap potential $V_k$.
--
--   **Formalization Note** The definition takes the index $k$ of $L_k$ and computes with $k-1$. Along a DAM+ run $z_{k+1}$ equals the run's dual variable, because (4.6a) at $k=1$ forces $z_1=0$. $L_1$ divides by $A_0=0$; Lean returns $0$, and the paper's $L_1$ only appears multiplied by $A_0=0$ or $\rho_1=0$.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (4.3), p.15

import Definitions.Def_AccelSGDGrowth_cumWeight
import Definitions.Def_AccelSGDGrowth_phiStar

namespace AccelSGDGrowth

/-- The lower bound $L_k$ of Chen, Na, Kolar, arXiv:2006.06782v4, (4.3), p.15. For `k = j + 1`,
$$L_{j+1} = \frac{1}{A_j}\sum_{i=1}^j a_i\big[f(x_i) - \varepsilon_i^\top(x_\star - x_i)\big]
  - \frac{1}{A_j}\phi_j^\star(z_{j+1}) - \frac{1}{A_j}\sum_{i=1}^j a_i g_i^\top x_i,$$
with $\varepsilon_i = g_i - \nabla f(x_i)$ and $z_{j+1} = -\sum_{i=1}^j a_i g_i$ as in (4.2).

**Formalization Note.** `lowerL f m a x g xstar k` is $L_k$, computed with `j = k - 1`. The vector
$z_{j+1}$ is the explicit sum of (4.2); along a DAM+ run it equals the run's `z (j+1)`, because (4.6a)
at `k = 1` forces `z_1 = 0`. `L_1` divides by `A_0 = 0`; Lean returns `0`, and the paper's `L_1` only
ever appears multiplied by `A_0 = 0` or `ρ_1 = 0`. -/
noncomputable def lowerL {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℝ) (a : ℕ → ℝ)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d)) (k : ℕ) : ℝ :=
  1 / cumWeight a (k - 1) *
      ∑ i ∈ Finset.Icc 1 (k - 1),
        a i * (f (x i) - inner ℝ (g i - gradient f (x i)) (xstar - x i)) -
    1 / cumWeight a (k - 1) *
      phiStar m a x (k - 1) (-(∑ i ∈ Finset.Icc 1 (k - 1), a i • g i)) -
    1 / cumWeight a (k - 1) * ∑ i ∈ Finset.Icc 1 (k - 1), a i * inner ℝ (g i) (x i)

end AccelSGDGrowth


