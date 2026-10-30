-- Prove2me | Definitions.Def_AdaGradDHS_Diag_regret
-- name    : AdaGradDHS_Diag_regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:16:55.359824+00:00
-- url     : https://prove2.me/theorems/abccc75b-5405-4b06-9c79-48cc702aa9dd
-- title:
--   Composite regret $R_\varphi(T)$
-- statement:
--   Let $f_1, f_2, \dots$ be losses on $\mathbb{R}^d$, $\varphi$ a regularizer, $x_1, x_2, \dots$ the predictions, $x^* \in \mathbb{R}^d$ a comparator and $T \in \mathbb{N}$. The **regret** of the predictions with respect to $x^*$ over $T$ rounds is
--   $$R_\varphi(T) = \sum_{t=1}^T \big[ f_t(x_t) + \varphi(x_t) - f_t(x^*) - \varphi(x^*) \big].$$
--
--   This is the performance measure of all regret bounds in the paper: the cumulative composite loss $\phi_t = f_t + \varphi$ of the online predictions minus that of a fixed predictor $x^*$.
--
--   **Formalization Note** For $T = 0$ the regret is $0$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §1.1, p. 2123, eq. (2)

import Mathlib

namespace AdaGradDHS.Diag

/-- **Composite regret `R_φ(T)`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §1.1, p. 2123, eq. (2): "Rφ(T) ≜ Σ_{t=1}^T [φt(xt) − φt(x∗)] = Σ_{t=1}^T [ft(xt) + ϕ(xt) −
ft(x∗) − ϕ(x∗)]".

`regret f φ x xstar T = Σ_{t=1}^T (f_t(x_t) + φ(x_t) − f_t(x*) − φ(x*))`.

**Formalization Note.** Rounds are `t ∈ Finset.Icc 1 T`; for `T = 0` the regret is `0`. -/
def regret {d : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (f t (x t) + φ (x t) - f t xstar - φ xstar)

end AdaGradDHS.Diag


