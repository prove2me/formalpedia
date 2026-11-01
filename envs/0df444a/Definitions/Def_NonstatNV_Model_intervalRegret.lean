-- Prove2me | Definitions.Def_NonstatNV_Model_intervalRegret
-- name    : NonstatNV_Model_intervalRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:04:23.666022+00:00
-- url     : https://prove2.me/theorems/69ee14fb-57e7-4232-aa7f-43f0cfba334d
-- title:
--   Regret from period $a$ to period $b$
-- statement:
--   The **regret** of the orders $(q_t)$ on the instance $(\mu,b,h)$ from period $a$ to period $b$ is
--
--   $$
--   \mathbb E_{\mathbb P_\mu}\Big[\sum_{t=a}^{b}\big(C_t(\mu_t,q_t)-C_t(\mu_t,q_t^*)\big)\Big],
--   $$
--
--   the expectation over independent demands $d_t\sim D_{\mu_t}$. The regret over the horizon is the case $a=1$, $b=T$. The worst-case regrets $\mathcal R^\pi(T)$ and $\mathcal R^\pi(T)[a,b]$ of the paper are suprema of this quantity over the instance class; the mission states its bounds for every instance of the class, which is equivalent.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, §2.3, p.14; p.34

import Definitions.Def_NonstatNV_Model_opt
import Definitions.Def_NonstatNV_Model_demandLaw

open MeasureTheory

namespace NonstatNV

/-- The regret incurred from period `lo` to period `hi` by the orders `q` on the instance
`(μ, b, h)` (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.14 and p.34):
`E[Σ_{t=lo}^{hi} (C_t(μ_t, q_t) − C_t(μ_t, q*_t))]`, the expectation over independent demands
`d_t ∼ D_{μ_t}`. The regret of a policy over the horizon is `intervalRegret … 1 T`.

**Formalization Note** The worst-case regret `R^π(T)` and `R^π(T)[a, b]` of the paper are suprema
of this quantity over the instance class; every statement of the mission bounds it for every instance
of the class, which is equivalent. `q t ω` is the order of period `t` on the demand path `ω`. -/
noncomputable def Model.intervalRegret (M : Model) (μ b h : ℕ → ℝ) (q : ℕ → (ℕ → ℝ) → ℝ)
    (lo hi : ℕ) : ℝ :=
  ∫ ω, (∑ t ∈ Finset.Icc lo hi, (M.cost (μ t) (b t) (h t) (q t ω) - M.opt (μ t) (b t) (h t)))
    ∂(M.demandLaw μ)

end NonstatNV


