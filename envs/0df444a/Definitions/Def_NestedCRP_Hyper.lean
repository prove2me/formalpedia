-- Prove2me | Definitions.Def_NestedCRP_Hyper
-- name    : NestedCRP_Hyper
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:30.151972+00:00
-- url     : https://prove2.me/theorems/53746154-2d24-4b4e-8666-0d2b8f239030
-- title:
--   Hyperparameters of hLDA
-- statement:
--   The hyperparameters of hierarchical latent Dirichlet allocation, together with their ranges: the Chinese restaurant process parameter $\gamma>0$, the topic Dirichlet parameter $\eta>0$, and the stick parameters $m\in(0,1)$ and $\pi>0$ of the two-parameter distribution $\mathrm{GEM}(m,\pi)$.
--
--   Bundling the ranges keeps every later statement free of side conditions, and it is what makes each Beta and Dirichlet law below a probability measure.
--
--   **Formalization Note** The field `pi` is the paper's $\pi$, not the circle constant. The paper states $m\in(0,1)$ and $\pi>0$ on p.7:8; $\gamma>0$ and $\eta>0$ are implied by Eq. (1) being a probability law and by the requirement $\alpha_i>0$ on Dirichlet parameters. The hyperparameters are fixed throughout, as the conditioning in Eqs. (2) and (4) fixes them.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §2.2 p.7:6, §2.3 p.7:8, §4 p.7:11

import Mathlib

namespace NestedCRP

/-- The hyperparameters of hLDA with their ranges: the CRP parameter `gamma > 0` of Eq. (1), the
topic Dirichlet parameter `eta > 0`, and the parameters `m ∈ (0,1)`, `pi > 0` of GEM(m, π).
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §2.2 p.7:6, §2.3 p.7:8, §4 p.7:11.

**Formalization Note** The field `pi` is the paper's π, not the circle constant. The paper states
`m ∈ (0,1)` and `π > 0` on p.7:8; `gamma > 0` and `eta > 0` are implied by Eq. (1) being a law and
by "`αi > 0`" for Dirichlet parameters (p.7:6). The hyperparameters are fixed, as the conditioning
in Eqs. (2) and (4) fixes them; the sampling of §5.4 is out of scope. -/
structure Hyper where
  gamma : ℝ
  eta : ℝ
  m : ℝ
  pi : ℝ
  gamma_pos : 0 < gamma
  eta_pos : 0 < eta
  m_pos : 0 < m
  m_lt_one : m < 1
  pi_pos : 0 < pi

end NestedCRP


