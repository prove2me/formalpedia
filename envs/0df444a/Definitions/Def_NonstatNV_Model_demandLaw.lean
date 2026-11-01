-- Prove2me | Definitions.Def_NonstatNV_Model_demandLaw
-- name    : NonstatNV_Model_demandLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:47.879022+00:00
-- url     : https://prove2.me/theorems/601e129c-0745-43ee-9c36-7093c7859cea
-- title:
--   Joint law of independent demands $\bigotimes_t D_{\mu_t}$
-- statement:
--   For a sequence of means $(\mu_t)$, the **joint law of the demands** is the product measure
--
--   $$
--   \mathbb P_\mu=\bigotimes_{t} D_{\mu_t}
--   $$
--
--   on demand paths $\omega=(\omega_t)_t$, under which the coordinate $\omega_t$ is the demand $d_t$ of period $t$ and the demands are independent over time, as the paper assumes.
--
--   **Formalization Note** Paths are indexed by all $t\in\mathbb N$; the periods of the problem are $t=1,\dots,T$ and no policy or regret uses the other coordinates.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, §2, p.9

import Definitions.Def_NonstatNV_Model

open MeasureTheory

namespace NonstatNV

/-- The joint law of the demands for a sequence of means `μ` (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, §2, p.9: "the period's
demand d_t is drawn from … D_t … These demand distributions are independent over time"): the product
measure `⊗_t D_{μ_t}` on `ℕ → ℝ`, under which the coordinate `ω t` is the demand `d_t`.

**Formalization Note** Periods are `t = 1, …, T`; coordinates `t = 0` and `t > T` are never used by
any policy or regret below. Independence over time is the product structure. -/
noncomputable def Model.demandLaw (M : Model) (μ : ℕ → ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun t => (M.D (μ t) : Measure ℝ)

end NonstatNV


