-- Prove2me | Definitions.Def_AccelSGDGrowth_gapV
-- name    : AccelSGDGrowth_gapV
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:38.762251+00:00
-- url     : https://prove2.me/theorems/b3e10e95-468d-41a8-a403-eb9122aaba00
-- title:
--   The potential $V_k=f(y_k)-L_k$
-- statement:
--   The duality-gap potential of the analysis framework: $U_k=f(y_k)$ is an upper bound and $L_k$ of (4.3) a lower bound of $f(x_\star)$, and
--   $$
--   V_k=U_k-L_k=f(y_k)-L_k .
--   $$
--   For $k\ge2$, $f(y_k)-f(x_\star)\le V_k$, so $V_k\ge0$; Theorem 4.1 is a recursion for $\mathbb EV_k$.
--
--   **Formalization Note** $V_1$ contains the junk value $L_1$ (division by $A_0=0$); it only enters multiplied by $A_0=0$ or $\rho_1=0$.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, p.16 (analysis framework, Step 1) and Theorem 4.1, p.18

import Definitions.Def_AccelSGDGrowth_lowerL

namespace AccelSGDGrowth

/-- The potential (gap) $V_k = U_k - L_k$ with $U_k = f(y_k)$ and $L_k$ of (4.3) (Chen, Na, Kolar,
arXiv:2006.06782v4, §4 "Analysis framework", p.16, and Theorem 4.1, p.18).

**Formalization Note.** `V_1` contains the junk `L_1` (division by `A_0 = 0`); it only enters
multiplied by `A_0 = 0` or `ρ_1 = 0`. -/
noncomputable def gapV {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℝ) (a : ℕ → ℝ)
    (x y g : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d)) (k : ℕ) : ℝ :=
  f (y k) - lowerL f m a x g xstar k

end AccelSGDGrowth


