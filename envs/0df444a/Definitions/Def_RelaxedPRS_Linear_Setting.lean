-- Prove2me | Definitions.Def_RelaxedPRS_Linear_Setting
-- name    : RelaxedPRS_Linear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:14.995155+00:00
-- url     : https://prove2.me/theorems/44404767-0ae8-488b-84ca-61ecba1f7d98
-- title:
--   Theorems 4.1–4.3, pp. 14–16 — the contraction factors C(λ) of the three linear-convergence theorems
-- statement:
--   The relaxed Peaceman–Rachford objects of §1.2–§1.10 (the reflection $R_P=2P-I$, $T_{\rm PRS}=R_{P_f}\circ R_{P_g}$, Algorithm 1, the auxiliary points $x_g,x_f$, the selected proximal subgradients, strong convexity, $(1/\beta)$-Lipschitz gradients, the auxiliary term $S_f$ and the objective error) are taken from the shared modules `RelaxedPRS.StrongCvx.Setting` and `RelaxedPRS.BestIter.Setting`. This module adds the three explicit contraction factors of Section 4. For $\gamma>0$, regularity parameters $\mu,\beta$ and a relaxation parameter $\lambda$,
--
--   $$
--   C_{4.1}(\lambda)=\Bigl(1-\frac{4\gamma\lambda\mu_g}{(1+\gamma/\beta_g)^2}\Bigr)^{1/2},\qquad
--   C_{4.2}(\lambda)=\Bigl(1-\frac{\lambda}{2}\min\Bigl\{\frac{4\gamma\mu_f}{(1+\gamma/\beta_f)^2},1-\lambda\Bigr\}\Bigr)^{1/2},
--   $$
--
--   $$
--   C_{4.3}(\lambda)=\Bigl(1-\frac{4\lambda}{3}\min\Bigl\{\gamma\mu,\frac{\beta}{\gamma},1-\lambda\Bigr\}\Bigr)^{1/2},
--   $$
--
--   the factors of Theorems 4.1, 4.2 and 4.3.
--
--   **Formalization Note** The square root is `Real.sqrt`, which returns $0$ on a negative radicand. For $0\le\lambda\le1$ the radicands of $C_{4.2}$ and $C_{4.3}$ are at least $7/8$ and $2/3$; the radicand of $C_{4.1}$ is nonnegative whenever $\mu_g$-strong convexity and a $(1/\beta_g)$-Lipschitz gradient coexist on a nonzero space (then $\mu_g\beta_g\le1$).
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, pp. 4–8, §1.2, Algorithm 1, Lemma 1.1, (1.14), and pp. 14–16, Theorems 4.1–4.3

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_BestIter_Setting
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

namespace RelaxedPRS.Linear

/-- The factor in Theorem 4.1, p. 14. -/
noncomputable def C41 (γ μg βg t : ℝ) : ℝ :=
  Real.sqrt (1 - 4 * γ * t * μg / (1 + γ / βg) ^ 2)

/-- The factor in Theorem 4.2, p. 15. -/
noncomputable def C42 (γ μf βf t : ℝ) : ℝ :=
  Real.sqrt (1 - t / 2 * min (4 * γ * μf / (1 + γ / βf) ^ 2) (1 - t))

/-- The factor in Theorem 4.3, p. 16. -/
noncomputable def C43 (γ μ β t : ℝ) : ℝ :=
  Real.sqrt (1 - 4 * t / 3 * min (min (γ * μ) (β / γ)) (1 - t))

end RelaxedPRS.Linear


